{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | The type checker: type inference, weak head normalization, and definitional equality, following the
-- algorithm of the Lean 4 kernel (lazy delta reduction guided by reducibility hints, proof irrelevance, eta for
-- functions and structures, K-like reduction, native @Nat@ and @String@ literals). One 'TC' checks one
-- declaration; its caches are private to it.
module Tenet.TypeChecker
  ( TC (..), LocalDecl (..), newTC, newTCWith
  , infer, check, checkWith, whnf, whnfCore, isDefEq, isProp
  , ensureSort, ensurePi, ensureType, ensureSortLevel
  , mkLocalDecl, mkLetDecl, getLocalDecl, mkPiFVars, mkLambdaFVars, fvarIdOf
  , isNonRecStructure, natLitToConstructor, stringLitToConstructor
  , primitiveOk, unvalidatedPrimitives
  , showExprLC, withFaithful
  ) where

import Control.Exception (SomeException, throwIO, try, fromException)
import Control.Monad
import Data.Bits
import Data.IORef
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import Data.Maybe (isJust)
import qualified Data.Text as T
import GHC.Num.Integer (integerLog2)
import System.IO.Unsafe (unsafePerformIO)
import Tenet.Env
import Tenet.Expr
import Tenet.ExprOps
import Tenet.Level
import Tenet.Name

-- ---------------------------------------------------------------- local context

data LocalDecl = LocalDecl
  { ldName :: !Name
  , ldType :: Expr
  , ldValue :: Maybe Expr
  , ldInfo :: !BinderInfo
  }

{-# NOINLINE fvarCounter #-}
fvarCounter :: IORef Int
fvarCounter = unsafePerformIO (newIORef 0)

freshId :: IO Int
freshId = atomicModifyIORef' fvarCounter (\n -> (n + 1, n))

-- ---------------------------------------------------------------- caches

type HCache v = IORef (IM.IntMap [(Expr, v)])

newCache :: IO (HCache v)
newCache = newIORef IM.empty

cacheGet :: HCache v -> Expr -> IO (Maybe v)
cacheGet c e = do
  m <- readIORef c
  pure $ case IM.lookup (exprHash e) m of
    Nothing -> Nothing
    Just b -> go b
  where
    go [] = Nothing
    go ((k, v) : rest) = if k == e then Just v else go rest

cachePut :: HCache v -> Expr -> v -> IO ()
cachePut c e v = modifyIORef' c (IM.insertWith (++) (exprHash e) [(e, v)])

type PairSet = IORef (IM.IntMap [(Expr, Expr)])

pairKey :: Expr -> Expr -> Int
pairKey a b = exprHash a + exprHash b

pairHas :: PairSet -> Expr -> Expr -> IO Bool
pairHas ps a b = do
  m <- readIORef ps
  pure $ case IM.lookup (pairKey a b) m of
    Nothing -> False
    Just bucket -> any (\(x, y) -> (x == a && y == b) || (x == b && y == a)) bucket

pairPut :: PairSet -> Expr -> Expr -> IO ()
pairPut ps a b = modifyIORef' ps (IM.insertWith (++) (pairKey a b) [(a, b)])

-- ---------------------------------------------------------------- the checker

data TC = TC
  { tcEnv :: Env
  , tcLctx :: IORef (IM.IntMap LocalDecl)
  , tcSafety :: !Safety
  , tcSkipPrims :: !Bool
  , tcCacheFailures :: !Bool
  , tcLParams :: IORef (Maybe [Name])
  , tcEager :: IORef Bool
  , tcUnfolds :: IORef Int
  , tcInferOnly :: HCache Expr
  , tcCheckC :: HCache Expr
  , tcWhnfCoreC :: HCache Expr
  , tcWhnfC :: HCache Expr
  , tcUnfoldC :: HCache Expr
  , tcSuccess :: PairSet
  , tcFailure :: PairSet
  }

{-# NOINLINE faithfulRef #-}
faithfulRef :: IORef Bool
faithfulRef = unsafePerformIO (newIORef False)

-- | Run an action with failure caching off for every checker created inside it: the reference algorithm exactly.
withFaithful :: IO a -> IO a
withFaithful act = do
  saved <- readIORef faithfulRef
  writeIORef faithfulRef True
  r <- tryAny act
  writeIORef faithfulRef saved
  either throwIO pure r

newTC :: Env -> Safety -> IO TC
newTC env safety = do
  l <- newIORef IM.empty
  newTCWith env l safety False True

-- | A checker sharing a given local context.
newTCWith :: Env -> IORef (IM.IntMap LocalDecl) -> Safety -> Bool -> Bool -> IO TC
newTCWith env lctx safety skipPrims cacheFailures = do
  lp <- newIORef Nothing
  eager <- newIORef False
  unf <- newIORef 0
  c1 <- newCache
  c2 <- newCache
  c3 <- newCache
  c4 <- newCache
  c5 <- newCache
  s <- newIORef IM.empty
  f <- newIORef IM.empty
  faithful <- readIORef faithfulRef
  pure TC { tcEnv = env, tcLctx = lctx, tcSafety = safety, tcSkipPrims = skipPrims, tcCacheFailures = cacheFailures && not faithful
          , tcLParams = lp, tcEager = eager, tcUnfolds = unf
          , tcInferOnly = c1, tcCheckC = c2, tcWhnfCoreC = c3, tcWhnfC = c4, tcUnfoldC = c5
          , tcSuccess = s, tcFailure = f }

mkLocalDecl :: TC -> Name -> Expr -> BinderInfo -> IO Expr
mkLocalDecl tc n ty bi = do
  i <- freshId
  modifyIORef' (tcLctx tc) (IM.insert i (LocalDecl n ty Nothing bi))
  pure (FVar i)

mkLetDecl :: TC -> Name -> Expr -> Expr -> IO Expr
mkLetDecl tc n ty v = do
  i <- freshId
  modifyIORef' (tcLctx tc) (IM.insert i (LocalDecl n ty (Just v) BDefault))
  pure (FVar i)

fvarIdOf :: Expr -> IO Int
fvarIdOf (FVar i) = pure i
fvarIdOf e = kerr ("expected a free variable, got " ++ showExpr e)

getLocalDecl :: TC -> Expr -> IO LocalDecl
getLocalDecl tc (FVar i) = do
  m <- readIORef (tcLctx tc)
  maybe (kerr "unknown free variable") pure (IM.lookup i m)
getLocalDecl _ e = kerr ("expected a free variable, got " ++ showExpr e)

findLocalDecl :: TC -> Int -> IO (Maybe LocalDecl)
findLocalDecl tc i = IM.lookup i <$> readIORef (tcLctx tc)

mkBinding :: TC -> Bool -> [Expr] -> Expr -> Bool -> IO Expr
mkBinding tc isLam fvars body removeDeadLet = do
  ids <- mapM fvarIdOf fvars
  decls <- mapM (getLocalDecl tc) fvars
  let r0 = abstractFVars body ids
      step r (i, decl) =
        let prefix = take i ids
        in case ldValue decl of
             Just val ->
               if not removeDeadLet || hasLooseBVar r 0
                 then Let (ldName decl) (abstractFVars (ldType decl) prefix) (abstractFVars val prefix) r
                 else lowerLooseBVars r 1 1
             Nothing ->
               let ty = abstractFVars (ldType decl) prefix
               in if isLam then Lam (ldName decl) (ldInfo decl) ty r else Pi (ldName decl) (ldInfo decl) ty r
  pure (foldl step r0 (reverse (zip [0 ..] decls)))

mkPiFVars :: TC -> [Expr] -> Expr -> IO Expr
mkPiFVars tc fvars body = mkBinding tc False fvars body False

mkLambdaFVars :: TC -> [Expr] -> Expr -> IO Expr
mkLambdaFVars tc fvars body = mkBinding tc True fvars body False

showExprLC :: TC -> Expr -> IO String
showExprLC _ e = pure (trunc (showExpr e))
  where trunc s = if length s > 600 then take 600 s ++ "…" else s

-- ---------------------------------------------------------------- well-known names

nNat, nNatZero, nNatSucc, nBoolTrue, nBoolFalse, nEagerReduce, nReduceBool, nReduceNat :: Name
nNat = nameOf ["Nat"]
nNatZero = nameOf ["Nat", "zero"]
nNatSucc = nameOf ["Nat", "succ"]
nBoolTrue = nameOf ["Bool", "true"]
nBoolFalse = nameOf ["Bool", "false"]
nEagerReduce = nameOf ["eagerReduce"]
nReduceBool = nameOf ["Lean", "reduceBool"]
nReduceNat = nameOf ["Lean", "reduceNat"]

natZeroE, boolTrueE, boolFalseE, natE, stringE :: Expr
natZeroE = Const nNatZero []
boolTrueE = Const nBoolTrue []
boolFalseE = Const nBoolFalse []
natE = Const nNat []
stringE = Const (nameOf ["String"]) []

dontCare :: Expr
dontCare = Const (nameOf ["dontcare"]) []

natMaxSizeBytes :: Integer
natMaxSizeBytes = 128 * 1024 * 1024

byteCount :: Integer -> Integer
byteCount n
  | n == 0 = 0
  | otherwise = (toInteger (integerLog2 (abs n)) + 8) `div` 8

checkNatSize :: Integer -> IO ()
checkNatSize numBytes =
  when (numBytes > natMaxSizeBytes) $
    kerr "the kernel refused a `Nat` numeral because its size exceeds the maximum"

-- ---------------------------------------------------------------- inference

ensureSortCore :: TC -> Expr -> Expr -> IO Expr
ensureSortCore tc e s = case e of
  Sort _ -> pure e
  _ -> do
    n <- whnf tc e
    case n of
      Sort _ -> pure n
      _ -> do
        a <- showExprLC tc s
        b <- showExprLC tc e
        kerr ("type expected, but got\n  " ++ a ++ "\nof type\n  " ++ b)

ensurePiCore :: TC -> Expr -> Expr -> IO Expr
ensurePiCore tc e s = case e of
  Pi {} -> pure e
  _ -> do
    n <- whnf tc e
    case n of
      Pi {} -> pure n
      _ -> do
        a <- showExprLC tc s
        b <- showExprLC tc e
        kerr ("function expected, but got\n  " ++ a ++ "\nof type\n  " ++ b)

ensureSort :: TC -> Expr -> IO Expr
ensureSort tc e = ensureSortCore tc e e

ensurePi :: TC -> Expr -> IO Expr
ensurePi tc e = ensurePiCore tc e e

-- | Ensure the type of @e@ is a sort and return that sort.
ensureType :: TC -> Expr -> IO Expr
ensureType tc e = do
  t <- infer tc e
  ensureSortCore tc t e

ensureSortLevel :: TC -> Expr -> IO Level
ensureSortLevel tc e = ensureSort tc e >>= \case
  Sort l -> pure l
  _ -> kerr "sort expected"

-- | @e@ is a proposition: its type is @Prop@ up to level normalization.
isProp :: TC -> Expr -> IO Bool
isProp tc e = do
  t <- infer tc e
  l <- ensureSortLevel tc t
  pure (normalizesToZero l)

infer :: TC -> Expr -> IO Expr
infer tc e = inferTypeCore tc e True

-- | Type check @e@, allowing only the given universe parameters, and return its type.
checkWith :: TC -> Expr -> [Name] -> IO Expr
checkWith tc e lps = do
  saved <- readIORef (tcLParams tc)
  writeIORef (tcLParams tc) (Just lps)
  r <- inferTypeCore tc e False `onExc` writeIORef (tcLParams tc) saved
  writeIORef (tcLParams tc) saved
  pure r

-- | Type check @e@ without restricting universe parameters.
check :: TC -> Expr -> IO Expr
check tc e = do
  saved <- readIORef (tcLParams tc)
  writeIORef (tcLParams tc) Nothing
  r <- inferTypeCore tc e False `onExc` writeIORef (tcLParams tc) saved
  writeIORef (tcLParams tc) saved
  pure r

onExc :: IO a -> IO () -> IO a
onExc act cleanup = do
  r <- tryAny act
  case r of
    Right v -> pure v
    Left ex -> cleanup >> throwIO ex

checkLevel :: TC -> Level -> IO ()
checkLevel tc l = do
  lp <- readIORef (tcLParams tc)
  case lp of
    Just ps | Just n <- getUndefParam ps l ->
      kerr ("invalid reference to undefined universe level parameter '" ++ showName n ++ "'")
    _ -> pure ()

inferConstant :: TC -> Name -> [Level] -> Bool -> IO Expr
inferConstant tc n ls inferOnly = do
  info <- getConst (tcEnv tc) n
  when (length (ciLParams info) /= length ls) $
    kerr ("incorrect number of universe levels parameters for '" ++ showName n ++ "', #"
          ++ show (length (ciLParams info)) ++ " expected, #" ++ show (length ls) ++ " provided")
  unless inferOnly $ do
    when (ciIsUnsafe info && tcSafety tc /= Unsafe) $
      kerr ("invalid declaration, it uses unsafe declaration '" ++ showName n ++ "'")
    case ciKind info of
      KDef { kSafety = Partial } | tcSafety tc == Safe ->
        kerr ("invalid declaration, safe declaration must not contain partial declaration '" ++ showName n ++ "'")
      _ -> pure ()
    mapM_ (checkLevel tc) ls
  pure (instantiateTypeLevelParams info ls)

instantiateTypeLevelParams :: ConstantInfo -> [Level] -> Expr
instantiateTypeLevelParams info ls
  | null ls = ciType info
  | otherwise = instantiateLevelParams (ciType info) (ciLParams info) ls

instantiateValueLevelParams :: ConstantInfo -> [Level] -> IO Expr
instantiateValueLevelParams info ls = case ciValue info of
  Nothing -> kerr ("'" ++ showName (ciName info) ++ "' has no value")
  Just v
    | length ls /= length (ciLParams info) -> kerr ("universe level mismatch instantiating value of '" ++ showName (ciName info) ++ "'")
    | null ls -> pure v
    | otherwise -> pure (instantiateLevelParams v (ciLParams info) ls)

inferLambda :: TC -> Expr -> Bool -> IO Expr
inferLambda tc e0 inferOnly = go [] e0
  where
    go fvs (Lam n bi dom body) = do
      let d = instantiateRev dom (reverse fvs)
      unless inferOnly $ void (inferTypeCore tc d inferOnly >>= \t -> ensureSortCore tc t d)
      fv <- mkLocalDecl tc n d bi
      go (fv : fvs) body
    go fvs e = do
      let fvars = reverse fvs
      r <- inferTypeCore tc (instantiateRev e fvars) inferOnly
      mkBinding tc False fvars (cheapBetaReduce r) False

inferPi :: TC -> Expr -> Bool -> IO Expr
inferPi tc e0 inferOnly = go [] [] e0
  where
    go fvs us (Pi n bi dom body) = do
      let d = instantiateRev dom (reverse fvs)
      t <- inferTypeCore tc d inferOnly
      Sort l <- ensureSortCore tc t d
      fv <- mkLocalDecl tc n d bi
      go (fv : fvs) (l : us) body
    go fvs us e = do
      let e' = instantiateRev e (reverse fvs)
      t <- inferTypeCore tc e' inferOnly
      Sort s <- ensureSortCore tc t e'
      pure (Sort (foldl (flip mkIMax) s us))
      -- us is innermost-first, so folding from the left wraps the innermost binder first

isEagerReduce :: Expr -> Bool
isEagerReduce e = isAppOfArity e nEagerReduce 2

inferApp :: TC -> Expr -> Bool -> IO Expr
inferApp tc e inferOnly
  | not inferOnly = case e of
      App f a -> do
        ft <- inferTypeCore tc f inferOnly
        Pi _ _ dom body <- ensurePiCore tc ft e
        aType <- inferTypeCore tc a inferOnly
        ok <- if isEagerReduce a
                then do
                  saved <- readIORef (tcEager tc)
                  writeIORef (tcEager tc) True
                  r <- isDefEq tc aType dom `onExc` writeIORef (tcEager tc) saved
                  writeIORef (tcEager tc) saved
                  pure r
                else isDefEq tc aType dom
        unless ok $ do
          s1 <- showExprLC tc e
          s2 <- showExprLC tc aType
          s3 <- showExprLC tc dom
          kerr ("application type mismatch in\n  " ++ s1 ++ "\nargument has type\n  " ++ s2 ++ "\nbut function expects\n  " ++ s3)
        pure (instantiate1 body a)
      _ -> kerr "application expected"
  | otherwise = do
      let f = getAppFn e
          args = getAppArgs e
      ft <- inferTypeCore tc f True
      loop ft [] args
  where
    loop fType pendingRev [] = pure (instantiateRev fType (reverse pendingRev))
    loop fType pendingRev (a : as) = case fType of
      Pi _ _ _ b -> loop b (a : pendingRev) as
      _ -> do
        t <- ensurePiCore tc (instantiateRev fType (reverse pendingRev)) e
        case t of
          Pi _ _ _ b -> loop b [a] as
          _ -> kerr "function expected"

inferLet :: TC -> Expr -> Bool -> IO Expr
inferLet tc e0 inferOnly = go [] e0
  where
    go fvs (Let n ty v body) = do
      let rev = reverse fvs
          type_ = instantiateRev ty rev
          val = instantiateRev v rev
      unless inferOnly $ do
        t <- inferTypeCore tc type_ inferOnly
        void (ensureSortCore tc t type_)
        valType <- inferTypeCore tc val inferOnly
        ok <- isDefEq tc valType type_
        unless ok $ do
          s1 <- showExprLC tc valType
          s2 <- showExprLC tc type_
          kerr ("type mismatch at let binding '" ++ showName n ++ "'\n  value has type\n  " ++ s1 ++ "\nbut is expected to have type\n  " ++ s2)
      fv <- mkLetDecl tc n type_ val
      go (fv : fvs) body
    go fvs e = do
      let fvars = reverse fvs
      r <- inferTypeCore tc (instantiateRev e fvars) inferOnly
      mkBinding tc False fvars (cheapBetaReduce r) True

inferProj :: TC -> Name -> Int -> Expr -> Bool -> IO Expr
inferProj tc sname idx struct inferOnly = do
  st <- inferTypeCore tc struct inferOnly
  type_ <- whnf tc st
  let ifn = getAppFn type_
      args = getAppArgs type_
      invalid = do
        s <- showExprLC tc (Proj sname idx struct)
        kerr ("invalid projection\n  " ++ s)
  ic <- case ifn of
    Const n ls | n == sname -> pure (n, ls)
    _ -> invalid
  ival <- getConst (tcEnv tc) (fst ic)
  (nparams, nindices, ctors) <- case ciKind ival of
    KInduct { kNumParams = p, kNumIndices = i, kCtors = cs } -> pure (p, i, cs)
    _ -> invalid
  ctorName <- case ctors of
    [c] | length args == nparams + nindices -> pure c
    _ -> invalid
  cinfo <- getConst (tcEnv tc) ctorName
  let r0 = instantiateTypeLevelParams cinfo (snd ic)
  r1 <- foldM (\r a -> do
                 r' <- whnf tc r
                 case r' of
                   Pi _ _ _ b -> pure (instantiate1 b a)
                   _ -> invalid) r0 (take nparams args)
  isPropType <- isProp tc type_
  r2 <- foldM (\r i -> do
                 r' <- whnf tc r
                 case r' of
                   Pi _ _ d b
                     | hasLooseBVars b -> do
                         when isPropType $ do
                           pd <- isProp tc d
                           unless pd invalid
                         pure (instantiate1 b (Proj (fst ic) i struct))
                     | otherwise -> pure b
                   _ -> invalid) r1 [0 .. idx - 1]
  r3 <- whnf tc r2
  case r3 of
    Pi _ _ d _ -> do
      when isPropType $ do
        pd <- isProp tc d
        unless pd invalid
      pure d
    _ -> invalid

-- | A literal's type is asserted by its representation rather than derived, so the environment has to agree
-- that the constant it names is the type the literal means.
inferLit :: TC -> Literal -> IO Expr
inferLit tc = \case
  NatLit n -> do
    checkNatSize (byteCount n)
    ok <- shortcut tc PNatLiteralType
    unless ok $ kerr "a numeric literal needs Nat to be the inductive type it denotes, with constructors Nat.zero and Nat.succ; this environment declares something else under that name"
    pure natE
  StrLit _ -> do
    ok <- shortcut tc PStringLiteralType
    unless ok $ kerr "a string literal needs String to be the type it denotes, reachable from a list of characters; this environment declares something else under that name"
    pure stringE

inferTypeCore :: TC -> Expr -> Bool -> IO Expr
inferTypeCore tc e inferOnly
  | hasLooseBVars e = kerr "type checker does not support loose bound variables, replace them with free variables before invoking it"
  | otherwise = do
      let cache = if inferOnly then tcInferOnly tc else tcCheckC tc
      hit <- cacheGet cache e
      case hit of
        Just r -> pure r
        Nothing -> do
          r <- case e of
            Lit l -> inferLit tc l
            Proj n i s -> inferProj tc n i s inferOnly
            FVar i -> do
              d <- findLocalDecl tc i
              maybe (kerr "unknown free variable") (pure . ldType) d
            Sort l -> do
              unless inferOnly (checkLevel tc l)
              pure (Sort (LSucc l))
            Const n ls -> inferConstant tc n ls inferOnly
            Lam {} -> inferLambda tc e inferOnly
            Pi {} -> inferPi tc e inferOnly
            App {} -> inferApp tc e inferOnly
            Let {} -> inferLet tc e inferOnly
            BVar _ -> kerr "unexpected bound variable"
          cachePut cache e r
          pure r

tryAny :: IO a -> IO (Either SomeException a)
tryAny = try

-- ---------------------------------------------------------------- inductive helpers used by reduction

isNonRecStructure :: Env -> Name -> IO Bool
isNonRecStructure env n = do
  c <- getConst env n
  pure $ case ciKind c of
    KInduct { kCtors = [_], kNumIndices = 0, kIsRec = False } -> True
    _ -> False

isConstructorApp :: Env -> Expr -> IO Bool
isConstructorApp env e = case getAppFn e of
  Const n _ -> do
    mc <- findConst env n
    pure $ case mc of
      Just ConstantInfo { ciKind = KCtor {} } -> True
      _ -> False
  _ -> pure False

natLitToConstructor :: Integer -> Expr
natLitToConstructor 0 = natZeroE
natLitToConstructor v = App (Const nNatSucc []) (mkNatLit (v - 1))

stringLitToConstructor :: Env -> T.Text -> IO Expr
stringLitToConstructor env s = do
  ctor <- stringLitCtor env
  let charT = Const (nameOf ["Char"]) []
      consC = App (Const (nameOf ["List", "cons"]) [LZero]) charT
      nilC = App (Const (nameOf ["List", "nil"]) [LZero]) charT
      ofNat = Const (nameOf ["Char", "ofNat"]) []
      lst = foldr (\c acc -> mkApp consC [App ofNat (mkNatLit (toInteger (fromEnum c))), acc]) nilC (T.unpack s)
  pure (App (Const ctor []) lst)
  where stringLitCtor = stringLiteralConstructor

expandEtaStruct :: Env -> Expr -> Expr -> IO Expr
expandEtaStruct env eType e = case getAppFn eType of
  Const iname ls -> do
    ic <- getConst env iname
    case ciKind ic of
      KInduct { kCtors = (cn : _) } -> do
        ci <- getConst env cn
        case ciKind ci of
          KCtor { kNumParams = np, kNumFields = nf } -> do
            let base = mkApp (Const cn ls) (take np (getAppArgs eType))
            pure (foldl (\r i -> App r (Proj iname i e)) base [0 .. nf - 1])
          _ -> pure e
      _ -> pure e
  _ -> pure e

toCtorWhenK :: TC -> ConstantInfo -> Expr -> (Expr -> IO Expr) -> IO Expr
toCtorWhenK tc rec e whnf' = do
  appType <- infer tc e >>= whnf'
  mi <- recMajorInduct rec
  case getAppFn appType of
    Const n _ | n == mi -> do
      let nparams = case ciKind rec of KRec { kNumParams = p } -> p; _ -> 0
      mc <- mkNullaryCtor appType nparams
      case mc of
        Nothing -> pure e
        Just ctorApp -> do
          newType <- infer tc ctorApp
          ok <- isDefEq tc appType newType
          pure (if ok then ctorApp else e)
    _ -> pure e
  where
    mkNullaryCtor ty np = case getAppFn ty of
      Const dn ls -> do
        d <- getConst (tcEnv tc) dn
        case ciKind d of
          KInduct { kCtors = (c : _) } -> pure (Just (mkApp (Const c ls) (take np (getAppArgs ty))))
          _ -> pure Nothing
      _ -> pure Nothing

toCtorWhenStructure :: TC -> Name -> Expr -> (Expr -> IO Expr) -> IO Expr
toCtorWhenStructure tc inductName e whnf' = do
  s <- isNonRecStructure (tcEnv tc) inductName
  c <- isConstructorApp (tcEnv tc) e
  if not s || c then pure e else do
    eType <- infer tc e >>= whnf'
    if not (isConstOf (getAppFn eType) inductName) then pure e else do
      p <- isProp tc eType
      if p then pure e else expandEtaStruct (tcEnv tc) eType e

-- | Iota reduction: reduce a recursor applied to a constructor application.
tryReduceRec :: TC -> Expr -> Name -> [Level] -> (Expr -> IO Expr) -> IO (Maybe Expr)
tryReduceRec tc e recName recLevels whnf' = do
  mrec <- findConst (tcEnv tc) recName
  case mrec of
    Just rec@ConstantInfo { ciKind = KRec { kNumParams = np, kNumMotives = nmot, kNumMinors = nmin, kK = isK } } -> do
      let recArgs = getAppArgs e
          majorIdx = recMajorIdx rec
      if majorIdx >= length recArgs then pure Nothing else do
        let major0 = recArgs !! majorIdx
        major1 <- if isK then toCtorWhenK tc rec major0 whnf' else pure major0
        major2 <- whnf' major1
        major3 <- case major2 of
          Lit (NatLit n) -> pure (natLitToConstructor n)
          Lit (StrLit s) -> stringLitToConstructor (tcEnv tc) s >>= whnf'
          _ -> do
            mi <- recMajorInduct rec
            toCtorWhenStructure tc mi major2 whnf'
        case recRuleFor rec major3 of
          Nothing -> pure Nothing
          Just rule -> do
            let majorArgs = getAppArgs major3
                nf = rrNumFields rule
            if nf > length majorArgs || length recLevels /= length (ciLParams rec) then pure Nothing else do
              let rhs0 = instantiateLevelParams (rrRhs rule) (ciLParams rec) recLevels
                  rhs1 = mkApp rhs0 (take (np + nmot + nmin) recArgs)
                  rhs2 = mkApp rhs1 (drop (length majorArgs - nf) majorArgs)
                  rhs3 = mkApp rhs2 (drop (majorIdx + 1) recArgs)
              pure (Just rhs3)
    _ -> pure Nothing

nQuotLift, nQuotInd, nQuotMk :: Name
nQuotLift = nameOf ["Quot", "lift"]
nQuotInd = nameOf ["Quot", "ind"]
nQuotMk = nameOf ["Quot", "mk"]

-- | @Quot.lift f h (Quot.mk r a)@ reduces to @f a@, and @Quot.ind h (Quot.mk r a)@ to @h a@.
quotTryReduceRec :: TC -> Expr -> Name -> IO (Maybe Expr)
quotTryReduceRec tc e fn
  | fn == nQuotLift = go 5 3
  | fn == nQuotInd = go 4 3
  | otherwise = pure Nothing
  where
    go mkPos argPos = do
      let args = getAppArgs e
      if length args <= mkPos then pure Nothing else do
        mk <- whnf tc (args !! mkPos)
        case (getAppFn mk, mk) of
          (Const n _, App _ a) | n == nQuotMk && getAppNumArgs mk == 3 ->
            pure (Just (mkApp (App (args !! argPos) a) (drop (mkPos + 1) args)))
          _ -> pure Nothing

-- ---------------------------------------------------------------- reduction

reduceRecursor :: TC -> Expr -> Expr -> Bool -> Bool -> IO (Maybe Expr)
reduceRecursor tc e hd cheapRec cheapProj = case hd of
  Const n ls -> do
    q <- quotInitialized (tcEnv tc)
    mq <- if q then quotTryReduceRec tc e n else pure Nothing
    case mq of
      Just r -> pure (Just r)
      Nothing -> tryReduceRec tc e n ls (\t -> if cheapRec then whnfCoreX tc cheapRec cheapProj t else whnf tc t)
  _ -> pure Nothing

reduceProjCore :: TC -> Expr -> Name -> Int -> IO (Maybe Expr)
reduceProjCore tc c0 sname idx = do
  c <- case c0 of
    Lit (StrLit s) -> stringLitToConstructor (tcEnv tc) s >>= whnf tc
    _ -> pure c0
  case getAppFn c of
    Const n _ -> do
      info <- getConst (tcEnv tc) n   -- `get`, as in Lean's reduce_proj_core
      case ciKind info of
        KCtor { kInduct = ind, kNumParams = np } | ind == sname ->
          let args = getAppArgs c in pure (if np + idx < length args then Just (args !! (np + idx)) else Nothing)
        _ -> pure Nothing
    _ -> pure Nothing

whnfCore :: TC -> Expr -> IO Expr
whnfCore tc = whnfCoreX tc False False

-- | Weak head normal form without delta reduction (beta, zeta, projection, iota, quotient).
whnfCoreX :: TC -> Bool -> Bool -> Expr -> IO Expr
whnfCoreX tc cheapRec cheapProj e = case e of
  FVar i -> do
    md <- findLocalDecl tc i
    case md >>= ldValue of
      Nothing -> pure e
      Just v -> whnfCoreX tc cheapRec cheapProj v
  Proj {} -> cached
  App {} -> cached
  Let {} -> cached
  _ -> pure e
  where
    recur = whnfCoreX tc cheapRec cheapProj
    cached = do
      hit <- cacheGet (tcWhnfCoreC tc) e
      case hit of
        Just r -> pure r
        Nothing -> do
          (r, store) <- compute
          when (store && not cheapRec && not cheapProj) $ cachePut (tcWhnfCoreC tc) e r
          pure r
    compute = case e of
      Proj n i s -> do
        c <- if cheapProj then recur s else whnf tc s
        m <- reduceProjCore tc c n i
        r <- maybe (pure e) recur m
        pure (r, True)
      App {} -> do
        let f0 = getAppFn e
            revArgs = getAppRevArgs e
        f <- recur f0
        case f of
          Lam {} -> do
            r <- recur (betaRev f revArgs)
            pure (r, True)
          _ | f == f0 -> do
                red <- reduceRecursor tc e f cheapRec cheapProj
                case red of
                  Just x -> do
                    r <- recur x
                    pure (r, False)
                  Nothing -> pure (e, False)
            | otherwise -> do
                r <- recur (mkRevApp f revArgs)
                pure (r, True)
      Let _ _ v b -> do
        r <- recur (instantiate1 b v)
        pure (r, True)
      _ -> pure (e, False)

-- | The definition to unfold if the head of @e@ is a delta-reducible constant.
isDelta :: TC -> Expr -> IO (Maybe ConstantInfo)
isDelta tc e = case getAppFn e of
  Const n ls -> do
    mi <- findConst (tcEnv tc) n
    pure $ case mi of
      Just info | isJust (ciValue info) && length ls == length (ciLParams info) -> Just info
      _ -> Nothing
  _ -> pure Nothing

unfoldDefinitionCore :: TC -> Expr -> IO (Maybe Expr)
unfoldDefinitionCore tc e = case e of
  Const _ ls -> do
    md <- isDelta tc e
    case md of
      Nothing -> pure Nothing
      Just d
        | null ls -> Just <$> instantiateValueLevelParams d ls
        | otherwise -> do
            hit <- cacheGet (tcUnfoldC tc) e
            case hit of
              Just r -> pure (Just r)
              Nothing -> do
                r <- instantiateValueLevelParams d ls
                cachePut (tcUnfoldC tc) e r
                pure (Just r)
  _ -> pure Nothing

-- | Unfold the head constant of @e@, if it is a definition or theorem.
unfoldDefinition :: TC -> Expr -> IO (Maybe Expr)
unfoldDefinition tc e = case e of
  App {} -> do
    mf <- unfoldDefinitionCore tc (getAppFn e)
    pure (fmap (\f -> mkRevApp f (getAppRevArgs e)) mf)
  _ -> unfoldDefinitionCore tc e

reduceNative :: Expr -> IO (Maybe Expr)
reduceNative = \case
  App (Const f _) (Const _ _) | f == nReduceBool || f == nReduceNat ->
    unsupported ("'" ++ showName f ++ "' requires running compiled code, which an external checker cannot trust; the declaration cannot be checked")
  _ -> pure Nothing

isNatLitExt :: Expr -> Bool
isNatLitExt e = e == natZeroE || isNatLit e

getNatVal :: Expr -> Integer
getNatVal (Lit (NatLit n)) = n
getNatVal _ = 0

-- | Whether the constant behind an accelerated path is the primitive it is named after. Dispatching on the name
-- alone lets an export declare @Nat.add@ as something else and have the kernel compute addition anyway.
shortcut :: TC -> Primitive -> IO Bool
shortcut tc p = if tcSkipPrims tc then pure True else primitiveOk (tcEnv tc) p

natArgs :: TC -> Expr -> IO (Maybe (Integer, Integer))
natArgs tc (App (App _ a1) a2) = do
  x <- whnf tc a1
  if not (isNatLitExt x) then pure Nothing else do
    y <- whnf tc a2
    pure (if isNatLitExt y then Just (getNatVal x, getNatVal y) else Nothing)
natArgs _ _ = pure Nothing

binOp :: TC -> Expr -> Bool -> (Integer -> Integer -> Integer) -> IO (Maybe Expr)
binOp tc e checkSize f = do
  m <- natArgs tc e
  case m of
    Nothing -> pure Nothing
    Just (x, y) -> do
      let r = f x y
      when checkSize $ checkNatSize (byteCount r)
      pure (Just (mkNatLit r))

binPred :: TC -> Expr -> (Integer -> Integer -> Bool) -> IO (Maybe Expr)
binPred tc e f = do
  m <- natArgs tc e
  pure $ case m of
    Nothing -> Nothing
    Just (x, y) -> Just (if f x y then boolTrueE else boolFalseE)

getCountArg :: Integer -> String -> IO Int
getCountArg c op
  | c > 4294967295 = kerr ("the kernel refused to evaluate `" ++ op ++ "` because its second argument does not fit in a 32-bit unsigned integer")
  | otherwise = pure (fromInteger (min c (toInteger (maxBound :: Int))))

reduceNat :: TC -> Expr -> IO (Maybe Expr)
reduceNat tc e = case getAppNumArgs e of
  1 | App (Const f []) a <- e, f == nNatSucc -> do
        ok <- shortcut tc PNatSucc
        if not ok then pure Nothing else do
          arg <- whnf tc a
          if not (isNatLitExt arg) then pure Nothing else do
            let v = getNatVal arg + 1
            checkNatSize (byteCount v)
            pure (Just (mkNatLit v))
  2 | App (App (Const f []) _) _ <- e -> dispatch f
  _ -> pure Nothing
  where
    dispatch f = case lookup f table of
      Nothing -> pure Nothing
      Just (p, act) -> do
        ok <- shortcut tc p
        if ok then act else pure Nothing
    nm s = nameOf ["Nat", s]
    table =
      [ (nm "add", (PNatAdd, binOp tc e True (+)))
      , (nm "sub", (PNatSub, binOp tc e True (\x y -> if x >= y then x - y else 0)))
      , (nm "mul", (PNatMul, binOp tc e True (*)))
      , (nm "pow", (PNatPow, reducePow))
      , (nm "gcd", (PNatGcd, binOp tc e False gcd))
      , (nm "mod", (PNatMod, binOp tc e False (\x y -> if y == 0 then x else x `mod` y)))
      , (nm "div", (PNatDiv, binOp tc e False (\x y -> if y == 0 then 0 else x `div` y)))
      , (nm "beq", (PNatBeq, binPred tc e (==)))
      , (nm "ble", (PNatBle, binPred tc e (<=)))
      , (nm "land", (PNatLand, binOp tc e False (.&.)))
      , (nm "lor", (PNatLor, binOp tc e False (.|.)))
      , (nm "xor", (PNatXor, binOp tc e False xor))
      , (nm "shiftLeft", (PNatShiftLeft, reduceShiftLeft))
      , (nm "shiftRight", (PNatShiftRight, binOp tc e False (\x y -> if y > toInteger (maxBound :: Int) then 0 else x `shiftR` fromInteger y)))
      ]
    reducePow = do
      m <- natArgs tc e
      case m of
        Nothing -> pure Nothing
        Just (b, ex) -> do
          k <- getCountArg ex "Nat.pow"
          when (b > 1 && k /= 0 && byteCount b > natMaxSizeBytes `div` toInteger k) $
            kerr "the kernel refused to evaluate `Nat.pow` because the result would exceed the maximum numeral size"
          pure (Just (mkNatLit (b ^ k)))
    reduceShiftLeft = do
      m <- natArgs tc e
      case m of
        Nothing -> pure Nothing
        Just (v, sh)
          | v == 0 -> pure (Just (mkNatLit 0))
          | otherwise -> do
              k <- getCountArg sh "Nat.shiftLeft"
              checkNatSize (byteCount v + toInteger (k `div` 8) + 1)
              pure (Just (mkNatLit (v `shiftL` k)))

bumpUnfold :: TC -> IO ()
bumpUnfold tc = do
  n <- readIORef (tcUnfolds tc)
  let mx = optMaxUnfolds (envOpts (tcEnv tc))
  when (n + 1 > mx) $ throwIO (Timeout mx)
  writeIORef (tcUnfolds tc) (n + 1)

-- | Weak head normal form, including delta reduction and literal arithmetic.
whnf :: TC -> Expr -> IO Expr
whnf tc e = case e of
  BVar _ -> pure e
  Sort _ -> pure e
  Pi {} -> pure e
  Lit _ -> pure e
  FVar i -> do
    md <- findLocalDecl tc i
    case md >>= ldValue of
      Nothing -> pure e
      Just _ -> go
  _ -> go
  where
    go = do
      hit <- cacheGet (tcWhnfC tc) e
      case hit of
        Just r -> pure r
        Nothing -> loop e
    loop t = do
      t1 <- whnfCore tc t
      mv <- reduceNative t1
      case mv of
        Just v -> done v
        Nothing -> do
          mn <- reduceNat tc t1
          case mn of
            Just v -> done v
            Nothing -> do
              next <- unfoldDefinition tc t1
              case next of
                Just n -> bumpUnfold tc >> loop n
                Nothing -> done t1
    done r = cachePut (tcWhnfC tc) e r >> pure r

-- ---------------------------------------------------------------- definitional equality

data LB = LTrue | LFalse | LUndef
  deriving (Eq)

toLB :: Bool -> LB
toLB True = LTrue
toLB False = LFalse

sameKind :: Expr -> Expr -> Bool
sameKind a b = tag a == tag b
  where
    tag :: Expr -> Int
    tag = \case
      BVar _ -> 0
      FVar _ -> 1
      Sort _ -> 2
      Const {} -> 3
      App {} -> 4
      Lam {} -> 5
      Pi {} -> 6
      Let {} -> 7
      Lit _ -> 8
      Proj {} -> 9

-- | A binder of the given kind (True: lambda).
bindingOf :: Bool -> Expr -> Maybe (Name, BinderInfo, Expr, Expr)
bindingOf True (Lam n bi d b) = Just (n, bi, d, b)
bindingOf False (Pi n bi d b) = Just (n, bi, d, b)
bindingOf _ _ = Nothing

isDefEqBinding :: TC -> Bool -> Expr -> Expr -> IO Bool
isDefEqBinding tc isLam = go []
  where
    go subst tt ss = case (bindingOf isLam tt, bindingOf isLam ss) of
      (Just (_, _, tdom, tbody), Just (sname, sinfo, sdom, sbody)) -> do
        let rev = reverse subst
        (ok, varS) <-
          if tdom /= sdom
            then do
              let vs = instantiateRev sdom rev
                  vt = instantiateRev tdom rev
              r <- isDefEq tc vt vs
              pure (r, Just vs)
            else pure (True, Nothing)
        if not ok then pure False else do
          s' <- if hasLooseBVars tbody || hasLooseBVars sbody
                  then do
                    let vs = maybe (instantiateRev sdom rev) id varS
                    fv <- mkLocalDecl tc sname vs sinfo
                    pure (fv : subst)
                  else pure (dontCare : subst)
          go s' tbody sbody
      _ -> let rev = reverse subst in isDefEq tc (instantiateRev tt rev) (instantiateRev ss rev)

quickIsDefEq :: TC -> Expr -> Expr -> IO LB
quickIsDefEq tc t s
  | t == s = pure LTrue
  | otherwise = do
      sb <- pairHas (tcSuccess tc) t s
      if sb then pure LTrue else
        if not (sameKind t s) then pure LUndef else case (t, s) of
          (Lam {}, _) -> toLB <$> isDefEqBinding tc True t s
          (Pi {}, _) -> toLB <$> isDefEqBinding tc False t s
          (Sort a, Sort b) -> pure (toLB (isEquiv a b))
          (Lit a, Lit b) -> pure (toLB (a == b))
          _ -> pure LUndef

isDefEqArgs :: TC -> Expr -> Expr -> IO Bool
isDefEqArgs tc (App tf ta) (App sf sa) = do
  ok <- isDefEq tc ta sa
  if ok then isDefEqArgs tc tf sf else pure False
isDefEqArgs _ t s = pure (not (isApp t) && not (isApp s))

isApp :: Expr -> Bool
isApp App {} = True
isApp _ = False

-- | Try to solve @(fun x, B) =?= s@ by eta-expanding @s@.
tryEtaExpansionCore :: TC -> Expr -> Expr -> IO Bool
tryEtaExpansionCore tc t s = case (t, s) of
  (Lam {}, Lam {}) -> pure False
  (Lam {}, _) -> do
    sType <- infer tc s >>= whnf tc
    case sType of
      Pi n bi d _ -> isDefEq tc t (Lam n bi d (App s (BVar 0)))
      _ -> pure False
  _ -> pure False

tryEtaExpansion :: TC -> Expr -> Expr -> IO Bool
tryEtaExpansion tc t s = do
  a <- tryEtaExpansionCore tc t s
  if a then pure True else tryEtaExpansionCore tc s t

-- | Is @s@ of the form @mk t.1 ... t.n@ for a structure constructor @mk@?
tryEtaStructCore :: TC -> Expr -> Expr -> IO Bool
tryEtaStructCore tc t s = case getAppFn s of
  Const fn _ -> do
    -- `get`, as in Lean: an unknown constant is a rejection, not a quiet "no eta"
    fi <- getConst (tcEnv tc) fn
    case ciKind fi of
      KCtor { kInduct = ind, kNumParams = np, kNumFields = nf }
        | getAppNumArgs s == np + nf -> do
            isStruct <- isNonRecStructure (tcEnv tc) ind
            if not isStruct then pure False else do
              tt <- infer tc t
              st <- infer tc s
              ok <- isDefEq tc tt st
              if not ok then pure False else
                allM (\(i, a) -> isDefEq tc (Proj ind (i - np) t) a) (drop np (zip [0 ..] (getAppArgs s)))
      _ -> pure False
  _ -> pure False

allM :: Monad m => (a -> m Bool) -> [a] -> m Bool
allM _ [] = pure True
allM f (x : xs) = f x >>= \b -> if b then allM f xs else pure False

tryEtaStruct :: TC -> Expr -> Expr -> IO Bool
tryEtaStruct tc t s = do
  a <- tryEtaStructCore tc t s
  if a then pure True else tryEtaStructCore tc s t

isDefEqApp :: TC -> Expr -> Expr -> IO Bool
isDefEqApp tc t s
  | App {} <- t, App {} <- s = do
      let tArgs = getAppArgs t
          sArgs = getAppArgs s
      if length tArgs /= length sArgs then pure False else do
        ok <- isDefEq tc (getAppFn t) (getAppFn s)
        if not ok then pure False else allM (uncurry (isDefEq tc)) (zip tArgs sArgs)
  | otherwise = pure False

isDefEqProofIrrel :: TC -> Expr -> Expr -> IO LB
isDefEqProofIrrel tc t s = do
  tType <- infer tc t
  p <- isProp tc tType
  if not p then pure LUndef else do
    sType <- infer tc s
    toLB <$> isDefEq tc tType sType

-- | If @e@ is @s.i ...@ and can be reduced by @whnf_core@, return the reduct.
tryUnfoldProjApp :: TC -> Expr -> IO (Maybe Expr)
tryUnfoldProjApp tc e = case getAppFn e of
  Proj {} -> do
    n <- whnfCore tc e
    pure (if n == e then Nothing else Just n)
  _ -> pure Nothing

data Step = Continue | DefUnknown | DefEqual | DefDiff

lazyDeltaReductionStep :: TC -> Expr -> Expr -> IO (Step, Expr, Expr)
lazyDeltaReductionStep tc tn sn = do
  bumpUnfold tc
  dt <- isDelta tc tn
  ds <- isDelta tc sn
  let unfoldT = do
        Just u <- unfoldDefinition tc tn
        whnfCoreX tc False True u
      unfoldS = do
        Just u <- unfoldDefinition tc sn
        whnfCoreX tc False True u
  r <- case (dt, ds) of
    (Nothing, Nothing) -> pure Nothing
    (Just _, Nothing) -> do
      m <- tryUnfoldProjApp tc sn
      case m of
        Just sn' -> pure (Just (Right (tn, sn')))
        Nothing -> unfoldT >>= \tn' -> pure (Just (Right (tn', sn)))
    (Nothing, Just _) -> do
      m <- tryUnfoldProjApp tc tn
      case m of
        Just tn' -> pure (Just (Right (tn', sn)))
        Nothing -> unfoldS >>= \sn' -> pure (Just (Right (tn, sn')))
    (Just dti, Just dsi) -> do
      let c = compareHints (ciHints dti) (ciHints dsi)
      if | c < 0 -> unfoldT >>= \tn' -> pure (Just (Right (tn', sn)))
         | c > 0 -> unfoldS >>= \sn' -> pure (Just (Right (tn, sn')))
         | otherwise -> do
             sameHead <-
               if isApp tn && isApp sn && ciName dti == ciName dsi && isRegular (ciHints dti)
                 then do
                   failed <- pairHas (tcFailure tc) tn sn
                   if failed then pure False else do
                     let Const _ l1 = getAppFn tn
                         Const _ l2 = getAppFn sn
                     ok <- if levelsEquiv l1 l2 then isDefEqArgs tc tn sn else pure False
                     if ok then pure True else pairPut (tcFailure tc) tn sn >> pure False
                 else pure False
             if sameHead then pure (Just (Left ())) else do
               tn' <- unfoldT
               sn' <- unfoldS
               pure (Just (Right (tn', sn')))
  case r of
    Nothing -> pure (DefUnknown, tn, sn)
    Just (Left ()) -> pure (DefEqual, tn, sn)
    Just (Right (tn', sn')) -> do
      q <- quickIsDefEq tc tn' sn'
      pure (case q of
              LTrue -> (DefEqual, tn', sn')
              LFalse -> (DefDiff, tn', sn')
              LUndef -> (Continue, tn', sn'))
  where
    isRegular (HRegular _) = True
    isRegular _ = False

isNatZero :: Expr -> Bool
isNatZero t = t == natZeroE || (case t of Lit (NatLit 0) -> True; _ -> False)

isNatSucc :: Expr -> Maybe Expr
isNatSucc = \case
  Lit (NatLit n) | n /= 0 -> Just (mkNatLit (n - 1))
  App (Const c []) a | c == nNatSucc -> Just a
  _ -> Nothing

isDefEqOffset :: TC -> Expr -> Expr -> IO LB
isDefEqOffset tc t s
  | isNatZero t && isNatZero s = pure LTrue
  | Just pt <- isNatSucc t, Just ps <- isNatSucc s = toLB <$> isDefEqCore tc pt ps
  | otherwise = pure LUndef

data DR = DRTrue | DRFalse | DRUndef Expr Expr

lazyDeltaReduction :: TC -> Expr -> Expr -> IO DR
lazyDeltaReduction tc = loop
  where
    loop tn sn = do
      r <- isDefEqOffset tc tn sn
      case r of
        LTrue -> pure DRTrue
        LFalse -> pure DRFalse
        LUndef -> do
          eager <- readIORef (tcEager tc)
          viaNat <-
            if (not (hasFVar tn) && not (hasFVar sn)) || eager
              then do
                tv <- reduceNat tc tn
                case tv of
                  Just v -> Just . toLB <$> isDefEqCore tc v sn
                  Nothing -> do
                    sv <- reduceNat tc sn
                    case sv of
                      Just v -> Just . toLB <$> isDefEqCore tc tn v
                      Nothing -> pure Nothing
              else pure Nothing
          case viaNat of
            Just LTrue -> pure DRTrue
            Just LFalse -> pure DRFalse
            _ -> do
              tnat <- reduceNative tn
              case tnat of
                Just v -> fin <$> isDefEqCore tc v sn
                Nothing -> do
                  snat <- reduceNative sn
                  case snat of
                    Just v -> fin <$> isDefEqCore tc tn v
                    Nothing -> do
                      (st, tn', sn') <- lazyDeltaReductionStep tc tn sn
                      case st of
                        Continue -> loop tn' sn'
                        DefUnknown -> pure (DRUndef tn' sn')
                        DefEqual -> pure DRTrue
                        DefDiff -> pure DRFalse
    fin True = DRTrue
    fin False = DRFalse

lazyDeltaProjReduction :: TC -> Expr -> Expr -> Name -> Int -> IO Bool
lazyDeltaProjReduction tc tn0 sn0 sname idx = loop tn0 sn0
  where
    loop tn sn = do
      (st, tn', sn') <- lazyDeltaReductionStep tc tn sn
      case st of
        Continue -> loop tn' sn'
        DefEqual -> pure True
        _ -> do
          mt <- reduceProjCore tc tn' sname idx
          case mt of
            Just t -> do
              ms <- reduceProjCore tc sn' sname idx
              case ms of
                Just s -> isDefEqCore tc t s
                Nothing -> isDefEqCore tc tn' sn'
            Nothing -> isDefEqCore tc tn' sn'

tryStringLitExpansionCore :: TC -> Expr -> Expr -> IO LB
tryStringLitExpansionCore tc t s = case (t, s) of
  (Lit (StrLit str), App (Const c []) _) -> do
    ctor <- stringLiteralConstructor (tcEnv tc)
    if c /= ctor then pure LUndef else do
      e <- stringLitToConstructor (tcEnv tc) str >>= whnf tc
      toLB <$> isDefEqCore tc e s
  _ -> pure LUndef

tryStringLitExpansion :: TC -> Expr -> Expr -> IO LB
tryStringLitExpansion tc t s = do
  r <- tryStringLitExpansionCore tc t s
  if r /= LUndef then pure r else tryStringLitExpansionCore tc s t

-- | Two terms of a structure type with one constructor and no fields are definitionally equal.
isDefEqUnitLike :: TC -> Expr -> Expr -> IO Bool
isDefEqUnitLike tc t s = do
  tType <- infer tc t >>= whnf tc
  case getAppFn tType of
    Const i _ -> do
      isStruct <- isNonRecStructure (tcEnv tc) i
      if not isStruct then pure False else do
        ival <- getConst (tcEnv tc) i
        case ciKind ival of
          KInduct { kCtors = (c : _) } -> do
            ci <- getConst (tcEnv tc) c
            case ciKind ci of
              KCtor { kNumFields = 0 } -> infer tc s >>= isDefEqCore tc tType
              _ -> pure False
          _ -> pure False
    _ -> pure False

isDefEqCore :: TC -> Expr -> Expr -> IO Bool
isDefEqCore tc t s = do
  r0 <- quickIsDefEq tc t s
  case r0 of
    LTrue -> pure True
    LFalse -> pure False
    LUndef -> do
      eager <- readIORef (tcEager tc)
      -- Proofs by reflection: a closed term against `Bool.true` is fully reduced.
      reflected <-
        if (not (hasFVar t) || eager) && isConstOf s nBoolTrue
          then (\w -> isConstOf w nBoolTrue) <$> whnf tc t
          else pure False
      if reflected then pure True else do
        tn <- whnfCoreX tc False True t
        sn <- whnfCoreX tc False True s
        r1 <- if not (tn == t) || not (sn == s) then quickIsDefEq tc tn sn else pure LUndef
        case r1 of
          LTrue -> pure True
          LFalse -> pure False
          LUndef -> do
            r2 <- isDefEqProofIrrel tc tn sn
            case r2 of
              LTrue -> pure True
              LFalse -> pure False
              LUndef -> do
                dr <- lazyDeltaReduction tc tn sn
                case dr of
                  DRTrue -> pure True
                  DRFalse -> pure False
                  DRUndef tn' sn' -> afterDelta tn' sn'
  where
    afterDelta tn sn
      | Const a la <- tn, Const b lb <- sn, a == b, levelsEquiv la lb = pure True
      | FVar a <- tn, FVar b <- sn, a == b = pure True
      | otherwise = do
          projOk <- case (tn, sn) of
            (Proj n1 i1 x, Proj n2 i2 y) | n1 == n2 && i1 == i2 -> lazyDeltaProjReduction tc x y n1 i1
            _ -> pure False
          if projOk then pure True else do
            tnn <- whnfCore tc tn
            snn <- whnfCore tc sn
            if not (tnn == tn) || not (snn == sn) then isDefEqCore tc tnn snn else do
              a <- isDefEqApp tc tn sn
              if a then pure True else do
                b <- tryEtaExpansion tc tn sn
                if b then pure True else do
                  c <- tryEtaStruct tc tn sn
                  if c then pure True else do
                    d <- tryStringLitExpansion tc tn sn
                    case d of
                      LTrue -> pure True
                      LFalse -> pure False
                      LUndef -> isDefEqUnitLike tc tn sn

-- | Definitional equality. Sound but incomplete; results are cached per checker.
isDefEq :: TC -> Expr -> Expr -> IO Bool
isDefEq tc t s = do
  failedBefore <- if tcCacheFailures tc then pairHas (tcFailure tc) t s else pure False
  if failedBefore then pure False else do
    r <- isDefEqCore tc t s
    if r then pairPut (tcSuccess tc) t s
      else when (tcCacheFailures tc) (pairPut (tcFailure tc) t s)
    pure r

-- ---------------------------------------------------------------- primitives
--
-- Reducing @Nat.add 2 2@ by adding two integers is a shortcut past the declaration's own body, taken on the
-- strength of the name alone. That is safe for Lean, which ships its prelude. It is not safe here: an export is
-- free to declare @Nat.add@ as anything of the right type. So a shortcut is taken only for a constant whose
-- defining equations have been checked. The equations are stated over free variables, which no accelerated path
-- can fire on. A constant that fails is not rejected: it is checked the ordinary way, by unfolding its body.

primName :: Primitive -> Name
primName = \case
  PNatLiteralType -> nameOf ["Nat"]
  PStringLiteralType -> nameOf ["String"]
  PNatSucc -> nameOf ["Nat", "succ"]
  PNatPred -> nameOf ["Nat", "pred"]
  PNatAdd -> nameOf ["Nat", "add"]
  PNatSub -> nameOf ["Nat", "sub"]
  PNatMul -> nameOf ["Nat", "mul"]
  PNatPow -> nameOf ["Nat", "pow"]
  PNatBeq -> nameOf ["Nat", "beq"]
  PNatBle -> nameOf ["Nat", "ble"]
  PNatDiv -> nameOf ["Nat", "div"]
  PNatMod -> nameOf ["Nat", "mod"]
  PNatGcd -> nameOf ["Nat", "gcd"]
  PNatLand -> nameOf ["Nat", "land"]
  PNatLor -> nameOf ["Nat", "lor"]
  PNatXor -> nameOf ["Nat", "xor"]
  PNatShiftLeft -> nameOf ["Nat", "shiftLeft"]
  PNatShiftRight -> nameOf ["Nat", "shiftRight"]

-- | Whether the kernel may short-circuit this primitive rather than unfold its body; decided once and remembered.
primitiveOk :: Env -> Primitive -> IO Bool
primitiveOk env p
  | not (optPrimitiveCheck (envOpts env)) = pure True
  | otherwise = do
      m <- readIORef (envPrims env)
      case M.lookup p m of
        Just b -> pure b
        Nothing -> do
          b <- checkPrimitive env p
          modifyIORef' (envPrims env) (M.insert p b)
          pure b

-- | The primitives this environment was asked about and refused to shortcut. Empty on a real Lean library.
unvalidatedPrimitives :: Env -> IO [Primitive]
unvalidatedPrimitives env = M.keys . M.filter not <$> readIORef (envPrims env)

checkPrimitive :: Env -> Primitive -> IO Bool
checkPrimitive env p = do
  r <- tryAny (checkPrimCore env p)
  case r of
    Right b -> pure b
    Left ex | Just (KernelError _) <- fromException ex -> pure False
            | otherwise -> throwIO ex

skipTC :: Env -> IO TC
skipTC env = do
  l <- newIORef IM.empty
  newTCWith env l Safe True True

sameType :: Env -> Expr -> Expr -> IO Bool
sameType env declared expected
  | declared == expected = pure True
  | otherwise = do
      r <- tryAny (skipTC env >>= \tc -> isDefEq tc declared expected)
      case r of
        Right b -> pure b
        Left ex | Just (KernelError _) <- fromException ex -> pure False
                | otherwise -> throwIO ex

checkPrimCore :: Env -> Primitive -> IO Bool
checkPrimCore env p
  | p == PStringLiteralType = checkStringLiteralType env
  | otherwise = do
      mnat <- findConst env nNat
      case mnat of
        Just ConstantInfo { ciKind = KInduct { kNumParams = 0, kNumIndices = 0, kCtors = [z, s] } }
          | z == nNatZero && s == nNatSucc -> do
              mz <- findConst env nNatZero
              ms <- findConst env nNatSucc
              case (mz, ms) of
                (Just zi@ConstantInfo { ciKind = KCtor {} }, Just si@ConstantInfo { ciKind = KCtor {} })
                  | ciType zi == natE && ciType si == mkArrow natE natE ->
                      if p == PNatLiteralType then pure True else checkOp
                _ -> pure False
        _ -> pure False
  where
    nat = natE
    zero = natZeroE
    succE e = App (Const nNatSucc []) e
    ok q = primitiveOk env q
    checkOp = do
      let name = primName p
      minfo <- findConst env name
      case minfo of
        Just info | null (ciLParams info) -> opWith info
        _ -> pure False
    opWith info
      | p == PNatSucc = case ciKind info of
          KCtor {} -> sameType env (ciType info) (mkArrow nat nat)
          _ -> pure False
      | otherwise = case ciKind info of
          KDef { kSafety = Safe } -> defWith info
          _ -> pure False
    defWith info = do
      let toBool = p `elem` [PNatBeq, PNatBle]
          result = if toBool then Const (nameOf ["Bool"]) [] else nat
          expected = if p == PNatPred then mkArrow nat nat else mkArrow nat (mkArrow nat result)
      boolOk <- if toBool then containsConst env (nameOf ["Bool"]) else pure True
      tyOk <- sameType env (ciType info) expected
      if not boolOk || not tyOk then pure False else equations
    equations = do
      tc <- skipTC env
      x <- mkLocalDecl tc (nameStr "x") nat BDefault
      y <- mkLocalDecl tc (nameStr "y") nat BDefault
      let f = Const (primName p) []
          ap1 a = App f a
          ap2 a b = mkApp f [a, b]
          eq a b = isDefEq tc a b
          trueE = Const (nameOf ["Bool", "true"]) []
          falseE = Const (nameOf ["Bool", "false"]) []
          natC s = Const (nameOf ["Nat", s]) []
      case p of
        PNatPred -> allM id [eq (ap1 zero) zero, eq (ap1 (succE x)) x]
        PNatAdd -> allM id [eq (ap2 x zero) x, eq (ap2 x (succE y)) (succE (ap2 x y))]
        PNatSub -> allM id [ok PNatPred, eq (ap2 x zero) x, eq (ap2 x (succE y)) (App (natC "pred") (ap2 x y))]
        PNatMul -> allM id [ok PNatAdd, eq (ap2 x zero) zero, eq (ap2 x (succE y)) (mkApp (natC "add") [ap2 x y, x])]
        PNatPow -> allM id [ok PNatMul, eq (ap2 x zero) (succE zero), eq (ap2 x (succE y)) (mkApp (natC "mul") [ap2 x y, x])]
        PNatBeq -> allM id [ eq (ap2 zero zero) trueE, eq (ap2 zero (succE y)) falseE
                           , eq (ap2 (succE x) zero) falseE, eq (ap2 (succE x) (succE y)) (ap2 x y) ]
        PNatBle -> allM id [ eq (ap2 zero zero) trueE, eq (ap2 zero (succE y)) trueE
                           , eq (ap2 (succE x) zero) falseE, eq (ap2 (succE x) (succE y)) (ap2 x y) ]
        _ -> allM (\(a, b, r) -> eq (ap2 (mkNatLit a) (mkNatLit b)) (mkNatLit r)) (samples p)

-- | Values at which a primitive with no checkable clause form is exercised: div, mod and gcd are well-founded
-- recursions and the bitwise operations recurse on a shifted argument, so an equation over free variables cannot
-- reduce. This detects a substituted implementation; it is a finite sample, not a proof of agreement everywhere.
samples :: Primitive -> [(Integer, Integer, Integer)]
samples = \case
  PNatDiv -> [(17, 5, 3), (5, 17, 0), (12, 3, 4), (7, 1, 7), (9, 0, 0), (0, 4, 0)]
  PNatMod -> [(17, 5, 2), (5, 17, 5), (12, 3, 0), (7, 1, 0), (9, 0, 9), (0, 4, 0)]
  PNatGcd -> [(12, 18, 6), (17, 5, 1), (0, 7, 7), (7, 0, 7), (9, 9, 9)]
  PNatLand -> [(12, 10, 8), (7, 8, 0), (255, 15, 15), (0, 9, 0)]
  PNatLor -> [(12, 10, 14), (7, 8, 15), (0, 9, 9), (5, 5, 5)]
  PNatXor -> [(12, 10, 6), (7, 8, 15), (0, 9, 9), (5, 5, 0)]
  PNatShiftLeft -> [(1, 4, 16), (3, 2, 12), (5, 0, 5), (0, 3, 0)]
  PNatShiftRight -> [(16, 4, 1), (12, 2, 3), (5, 0, 5), (3, 5, 0)]
  _ -> []

-- | A string literal is a term of the type named @String@, reduced through a constructor applied to a list of
-- characters. Both have to be what they are named.
checkStringLiteralType :: Env -> IO Bool
checkStringLiteralType env = do
  ms <- findConst env (nameOf ["String"])
  case ms of
    Just ConstantInfo { ciLParams = [], ciKind = KInduct { kNumParams = 0, kNumIndices = 0 } } -> do
      have <- mapM (containsConst env) [nameOf ["Char"], nameOf ["List"], nameOf ["Char", "ofNat"], nameOf ["List", "cons"], nameOf ["List", "nil"]]
      if not (and have) then pure False else do
        cname <- stringLiteralConstructor env
        mc <- findConst env cname
        case mc of
          Just ci | null (ciLParams ci) -> do
            let listChar = App (Const (nameOf ["List"]) [LZero]) (Const (nameOf ["Char"]) [])
            t <- sameType env (ciType ci) (mkArrow listChar stringE)
            if not t then pure False else do
              r <- tryAny $ do
                tc <- skipTC env
                built <- stringLitToConstructor env "a"
                ty <- check tc built
                isDefEq tc ty stringE
              case r of
                Right b -> pure b
                Left ex | Just (KernelError _) <- fromException ex -> pure False
                        | otherwise -> throwIO ex
          _ -> pure False
    _ -> pure False
