{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Inductive types: checking a (mutual, nested) declaration and deriving the constructors' metadata and the
-- recursors with their computation rules.
module Tenet.Inductive (addInductive, mkRecName) where

import Control.Monad
import Data.IORef
import Data.List (find)
import Data.Maybe (fromMaybe)
import qualified Data.Map.Strict as M
import Tenet.Env
import Tenet.Expr
import Tenet.ExprOps
import Tenet.Level
import Tenet.Name
import Tenet.TypeChecker

nestedPrefix :: Name
nestedPrefix = nameOf ["_nested"]

mkRecName :: Name -> Name
mkRecName n = mkStr n "rec"

showN :: Name -> String
showN = showName

-- ---------------------------------------------------------------- entry point

-- | Check an inductive declaration and add its types, constructors, and recursors to the environment.
addInductive :: Env -> IndDecl -> IO ()
addInductive env d = do
  forM_ (idTypes d) $ \t -> do
    checkNoFVar (itName t) (itType t)
    checkNoNestedAux (itName t) (itType t)
    forM_ (itCtors t) $ \c -> do
      checkNoFVar (cdName c) (cdType c)
      checkNoNestedAux (cdName c) (cdType c)
  checkUniformIndOccs d
  res <- elimNested env d
  let nnested = length (erAux2Nested res)
  auxEnv <- childEnv env []
  runAddInductive auxEnv (erAuxDecl res) nnested
  if nnested == 0
    then ownConstants auxEnv >>= mapM_ (addCore env)
    else restoreNested env auxEnv d res

checkNoFVar :: Name -> Expr -> IO ()
checkNoFVar n e = when (hasFVar e) $ kerr ("declaration '" ++ showN n ++ "' contains free variables")

checkNoNestedAux :: Name -> Expr -> IO ()
checkNoNestedAux n e =
  when (findE (\t _ -> case t of
                  Const c _ -> nestedPrefix `isPrefixOf` c
                  Proj c _ _ -> nestedPrefix `isPrefixOf` c
                  _ -> False) e) $
    kerr ("invalid declaration '" ++ showN n ++ "', it uses the reserved prefix '" ++ showN nestedPrefix ++ "'")

-- | Every occurrence of a type being declared must be applied to exactly the block's universe levels and parameters.
checkUniformIndOccs :: IndDecl -> IO ()
checkUniformIndOccs d = do
  let nparams = idNumParams d
      lvls = map LParam (idLParams d)
      indNames = map itName (idTypes d)
  forM_ (idTypes d) $ \t -> forM_ (itCtors t) $ \c ->
    forEachIO (\e offset -> case getAppFn e of
      Const fn fls | fn `elem` indNames -> do
        let args = getAppArgs e
        if length args > nparams then pure True else do
          let ok = length args == nparams && offset >= nparams && fls == lvls
                   && and [isBVarOf a (offset - 1 - i) | (i, a) <- zip [0 ..] args]
          unless ok $
            kerr ("invalid occurrence of datatype '" ++ showN fn ++ "' being declared: it must be applied to the parameters and universe levels of the mutual declaration")
          pure False
      _ -> pure True) (cdType c)

-- ---------------------------------------------------------------- the core: a mutual block without nested occurrences

data IC = IC
  { icEnv :: Env
  , icTc :: TC                  -- ^ holds the shared local context
  , icLParams :: [Name]
  , icNParams :: Int
  , icUnsafe :: Bool
  , icTypes :: [IndType]
  , icNNested :: Int
  , icLevels :: [Level]
  }

data Hdr = Hdr
  { hParams :: [Expr]
  , hNIndices :: [Int]
  , hResultLevel :: Level
  , hNotZero :: Bool
  , hIndConsts :: [Expr]
  }

data RecInfo = RecInfo { riC :: Expr, riIndices :: [Expr], riMajor :: Expr }

withTc :: IC -> IO TC
withTc ic = newTCWith (icEnv ic) (tcLctx (icTc ic)) (if icUnsafe ic then Unsafe else Safe) False True

mkLocal :: IC -> Name -> Expr -> BinderInfo -> IO Expr
mkLocal ic n t bi = mkLocalDecl (icTc ic) n (consumeTypeAnnotations t) bi

localForPi :: IC -> Expr -> IO Expr
localForPi ic (Pi n bi d _) = mkLocal ic n d bi
localForPi _ _ = kerr "expected a pi"

runAddInductive :: Env -> IndDecl -> Int -> IO ()
runAddInductive env d nnested = do
  tc0 <- newTC env (if idUnsafe d then Unsafe else Safe)
  let ic = IC { icEnv = env, icTc = tc0, icLParams = idLParams d, icNParams = idNumParams d, icUnsafe = idUnsafe d
              , icTypes = idTypes d, icNNested = nnested, icLevels = map LParam (idLParams d) }
  checkDuplicatedUnivParams (icLParams ic)
  hdr <- checkInductiveTypes ic
  declareInductiveTypes ic hdr
  checkConstructors ic hdr
  declareConstructors ic
  elimLevel <- initElimLevel ic hdr
  let kTarget = initKTarget ic hdr
  (infos, minors) <- mkRecInfos ic hdr elimLevel
  declareRecursors ic hdr elimLevel kTarget infos minors
  checkRecursors ic hdr elimLevel infos minors

checkInductiveTypes :: IC -> IO Hdr
checkInductiveTypes ic = go True (Hdr [] [] LZero False []) (icTypes ic)
  where
    env = icEnv ic
    np = icNParams ic
    go _ h [] = pure h { hNIndices = reverse (hNIndices h), hIndConsts = reverse (hIndConsts h) }
    go first h (it : rest) = do
      checkName env (itName it)
      checkName env (mkRecName (itName it))
      checkNoFVar (itName it) (itType it)
      tc <- withTc ic
      void (checkWith tc (itType it) (icLParams ic))
      t0 <- whnf tc (itType it)
      (params, nidx, tEnd) <- walk tc first (hParams h) 0 [] 0 t0
      when (length params /= np) $ kerr "number of parameters mismatch in inductive datatype declaration"
      s <- ensureSort tc tEnd
      lvl <- case s of Sort l -> pure l; _ -> kerr "sort expected"
      (rl, nz) <-
        if first then pure (lvl, isNotZero lvl)
        else if isEquiv lvl (hResultLevel h) then pure (hResultLevel h, hNotZero h)
        else kerr "mutually inductive types must live in the same universe"
      go False h { hParams = if first then params else hParams h
                 , hNIndices = nidx : hNIndices h, hResultLevel = rl, hNotZero = nz
                 , hIndConsts = Const (itName it) (icLevels ic) : hIndConsts h } rest
    -- returns (params, number of indices, final type)
    walk tc first params0 i acc nidx t = case t of
      Pi _ _ dom body
        | i < np -> do
            if first
              then do
                p <- localForPi ic t
                t' <- whnf tc (instantiate1 body p)
                walk tc first params0 (i + 1) (acc ++ [p]) nidx t'
              else do
                pty <- ldType <$> getLocalDecl tc (params0 !! i)
                ok <- isDefEq tc dom pty
                unless ok $ kerr "parameters of all inductive datatypes must match"
                t' <- whnf tc (instantiate1 body (params0 !! i))
                walk tc first params0 (i + 1) (acc ++ [params0 !! i]) nidx t'
        | otherwise -> do
            l <- localForPi ic t
            t' <- whnf tc (instantiate1 body l)
            walk tc first params0 (i + 1) acc (nidx + 1) t'
      _ -> pure (acc, nidx :: Int, t)

isIndOccIn :: [Expr] -> Expr -> Bool
isIndOccIn consts e = case e of
  Const c _ -> any (\k -> case k of Const kn _ -> kn == c; _ -> False) consts
  _ -> False

hasIndOcc :: Hdr -> Expr -> Bool
hasIndOcc h = findE (\e _ -> isIndOccIn (hIndConsts h) e)

isRecBlock :: Hdr -> [IndType] -> Bool
isRecBlock h types = or
  [ True
  | it <- types, c <- itCtors it
  , dom <- piDomains (cdType c)
  , hasIndOcc h dom ]
  where
    piDomains (Pi _ _ d b) = d : piDomains b
    piDomains _ = []

isReflexiveBlock :: IC -> Hdr -> IO Bool
isReflexiveBlock ic h = anyM (\it -> anyM (\c -> walk (cdType c)) (itCtors it)) (icTypes ic)
  where
    walk t@(Pi _ _ d b) =
      if isPi d && hasIndOcc h d then pure True else do
        l <- localForPi ic t
        walk (instantiate1 b l)
    walk _ = pure False
    isPi Pi {} = True
    isPi _ = False

anyM :: Monad m => (a -> m Bool) -> [a] -> m Bool
anyM _ [] = pure False
anyM f (x : xs) = f x >>= \b -> if b then pure True else anyM f xs

declareInductiveTypes :: IC -> Hdr -> IO ()
declareInductiveTypes ic h = do
  let rec_ = isRecBlock h (icTypes ic)
      allN = map itName (icTypes ic)
  refl <- isReflexiveBlock ic h
  forM_ (zip (icTypes ic) (hNIndices h)) $ \(it, nidx) -> do
    checkName (icEnv ic) (itName it)
    addCore (icEnv ic) (ConstantInfo (itName it) (icLParams ic) (itType it)
      (KInduct { kNumParams = icNParams ic, kNumIndices = nidx, kAll = allN, kCtors = map cdName (itCtors it)
               , kNumNested = icNNested ic, kIsRec = rec_, kUnsafe = icUnsafe ic, kReflexive = refl }))

-- | @t@ is @I params indices@ for the @i@-th type, with no occurrence of the block in the indices.
isValidIndAppAt :: IC -> Hdr -> Expr -> Int -> Bool
isValidIndAppAt ic h t i =
  let hd = getAppFn t
      args = getAppArgs t
      np = icNParams ic
  in hd == (hIndConsts h !! i)
     && length args == np + (hNIndices h !! i)
     && and (zipWith (==) (hParams h) (take np args))
     && not (any (hasIndOcc h) (drop np args))

isValidIndApp :: IC -> Hdr -> Expr -> Maybe Int
isValidIndApp ic h t = find (isValidIndAppAt ic h t) [0 .. length (icTypes ic) - 1]

-- | The index of the block type this argument recurses into, if it is a recursive argument.
isRecArgument :: IC -> Hdr -> Expr -> IO (Maybe Int)
isRecArgument ic h t0 = do
  tc <- withTc ic
  let go t = do
        t' <- whnf tc t
        case t' of
          Pi _ _ _ b -> do
            l <- localForPi ic t'
            go (instantiate1 b l)
          _ -> pure t'
  isValidIndApp ic h <$> go t0

checkPositivity :: IC -> Hdr -> Expr -> Name -> Int -> IO ()
checkPositivity ic h t0 ctorName argIdx = do
  tc <- withTc ic
  t <- whnf tc t0
  when (hasIndOcc h t) $ case t of
    Pi _ _ d b -> do
      when (hasIndOcc h d) $
        kerr ("arg #" ++ show (argIdx + 1) ++ " of '" ++ showN ctorName ++ "' has a non positive occurrence of the datatypes being declared")
      l <- localForPi ic t
      checkPositivity ic h (instantiate1 b l) ctorName argIdx
    _ -> case isValidIndApp ic h t of
      Nothing -> kerr ("arg #" ++ show (argIdx + 1) ++ " of '" ++ showN ctorName ++ "' contains a non valid occurrence of the datatypes being declared")
      Just _ -> pure ()

checkConstructors :: IC -> Hdr -> IO ()
checkConstructors ic h =
  forM_ (zip [0 ..] (icTypes ic)) $ \(idx, it) -> do
    foldM_ (\found c -> do
      let n = cdName c
      when (n `elem` found) $ kerr ("duplicate constructor name '" ++ showN n ++ "'")
      checkName (icEnv ic) n
      checkNoFVar n (cdType c)
      tc0 <- withTc ic
      void (checkWith tc0 (cdType c) (icLParams ic))
      walk n idx (0 :: Int) (cdType c)
      pure (n : found)) [] (itCtors it)
  where
    np = icNParams ic
    walk n idx i t = case t of
      Pi _ _ dom body
        | i < np -> do
            tc <- withTc ic
            pty <- ldType <$> getLocalDecl tc (hParams h !! i)
            ok <- isDefEq tc dom pty
            unless ok $ kerr ("arg #" ++ show (i + 1) ++ " of '" ++ showN n ++ "' does not match inductive datatypes parameters'")
            walk n idx (i + 1) (instantiate1 body (hParams h !! i))
        | otherwise -> do
            tc <- withTc ic
            sortE <- ensureType tc dom
            sl <- case sortE of Sort l -> pure l; _ -> kerr "sort expected"
            unless (isGeq (hResultLevel h) sl || normalizesToZero (hResultLevel h)) $
              kerr ("universe level of type_of(arg #" ++ show (i + 1) ++ ") of '" ++ showN n ++ "' is too big for the corresponding inductive datatype")
            unless (icUnsafe ic) $ checkPositivity ic h dom n i
            l <- localForPi ic t
            walk n idx (i + 1) (instantiate1 body l)
      _ -> unless (isValidIndAppAt ic h t idx) $ kerr ("invalid return type for '" ++ showN n ++ "'")

declareConstructors :: IC -> IO ()
declareConstructors ic =
  forM_ (icTypes ic) $ \it ->
    forM_ (zip [0 ..] (itCtors it)) $ \(cidx, c) -> do
      let arity = length (takeWhileCount (cdType c))
          nfields = arity - icNParams ic
      checkName (icEnv ic) (cdName c)
      addCore (icEnv ic) (ConstantInfo (cdName c) (icLParams ic) (cdType c)
        (KCtor { kInduct = itName it, kCidx = cidx, kNumParams = icNParams ic, kNumFields = nfields, kUnsafe = icUnsafe ic }))
  where
    takeWhileCount (Pi _ _ _ b) = () : takeWhileCount b
    takeWhileCount _ = []

-- | Can the recursor only eliminate into Prop?
elimOnlyAtUniverseZero :: IC -> Hdr -> IO Bool
elimOnlyAtUniverseZero ic h
  | hNotZero h = pure False
  | length (icTypes ic) > 1 = pure True
  | otherwise = case concatMap itCtors (take 1 (icTypes ic)) of
      [] -> pure False
      (_ : _ : _) -> pure True
      [ctor] -> do
        -- one constructor: every non-Prop field must appear in the result type
        let walk i t toCheck = case t of
              Pi _ _ dom body -> do
                fv <- localForPi ic t
                toCheck' <-
                  if i >= icNParams ic
                    then do
                      tc <- withTc ic
                      s <- ensureType tc dom
                      case s of
                        Sort l | not (normalizesToZero l) -> pure (fv : toCheck)
                        _ -> pure toCheck
                    else pure toCheck
                walk (i + 1 :: Int) (instantiate1 body fv) toCheck'
              _ -> pure (t, toCheck)
        (resT, toCheck) <- walk 0 (cdType ctor) []
        let resArgs = getAppArgs resT
        pure (any (\a -> a `notElem` resArgs) toCheck)

initElimLevel :: IC -> Hdr -> IO Level
initElimLevel ic h = do
  z <- elimOnlyAtUniverseZero ic h
  if z then pure LZero else do
    let fresh i u = if u `elem` icLParams ic then fresh (i + 1) (appendIndexAfter (nameStr "u") i) else u
    pure (LParam (fresh (1 :: Integer) (nameStr "u")))

initKTarget :: IC -> Hdr -> Bool
initKTarget ic h = case icTypes ic of
  [it] | normalizesToZero (hResultLevel h), [c] <- itCtors it -> countPis (cdType c) <= icNParams ic
  _ -> False
  where
    countPis (Pi _ _ _ b) = 1 + countPis b :: Int
    countPis _ = 0

getIIndices :: IC -> Hdr -> Expr -> IO (Int, [Expr])
getIIndices ic h t = case isValidIndApp ic h t of
  Nothing -> kerr "internal error: expected a valid inductive application"
  Just r -> pure (r, drop (icNParams ic) (getAppArgs t))

-- | The fields of a constructor, with the recursive ones marked, given the walk over its type.
ctorFields :: IC -> Hdr -> CtorDecl -> IO ([Expr], [Expr], Expr)
ctorFields ic h c = go (0 :: Int) (cdType c) [] []
  where
    go i t bu u = case t of
      Pi _ _ dom body
        | i < icNParams ic -> go (i + 1) (instantiate1 body (hParams h !! i)) bu u
        | otherwise -> do
            l <- localForPi ic t
            r <- isRecArgument ic h dom
            go (i + 1) (instantiate1 body l) (bu ++ [l]) (maybe u (const (u ++ [l])) r)
      _ -> pure (bu, u, t)

-- | For a recursive field @ui@: the binders of its type, and the block type it lands in with its indices.
recFieldInfo :: IC -> Hdr -> Expr -> IO ([Expr], Int, [Expr])
recFieldInfo ic h ui = do
  tc <- withTc ic
  uiTy0 <- infer tc ui >>= whnf tc
  let go t xs = case t of
        Pi _ _ _ b -> do
          x <- localForPi ic t
          t' <- whnf tc (instantiate1 b x)
          go t' (xs ++ [x])
        _ -> pure (t, xs)
  (uiTy, xs) <- go uiTy0 []
  (idx, inds) <- getIIndices ic h uiTy
  pure (xs, idx, inds)

mkRecInfos :: IC -> Hdr -> Level -> IO ([RecInfo], [[Expr]])
mkRecInfos ic h elimLevel = do
  tc <- withTc ic
  let ntypes = length (icTypes ic)
  infos <- forM (zip [0 ..] (icTypes ic)) $ \(dIdx, it) -> do
    t0 <- whnf tc (itType it)
    let go i t idxs = case t of
          Pi _ _ _ b
            | i < icNParams ic -> do
                t' <- whnf tc (instantiate1 b (hParams h !! i))
                go (i + 1) t' idxs
            | otherwise -> do
                l <- localForPi ic t
                t' <- whnf tc (instantiate1 b l)
                go (i + 1) t' (idxs ++ [l])
          _ -> pure idxs
    indices <- go (0 :: Int) t0 []
    major <- mkLocal ic (nameStr "t") (mkApp (mkApp (hIndConsts h !! dIdx) (hParams h)) indices) BDefault
    cTy0 <- mkPiFVars tc [major] (Sort elimLevel)
    cTy <- mkPiFVars tc indices cTy0
    let cName0 = nameStr "motive"
        cName = if ntypes > 1 then appendIndexAfter cName0 (toInteger dIdx + 1) else cName0
    c <- mkLocal ic cName cTy BDefault
    pure (RecInfo c indices major)
  minors <- forM (zip (icTypes ic) [0 :: Int ..]) $ \(it, _) ->
    forM (itCtors it) $ \ctor -> do
      (bu, u, t) <- ctorFields ic h ctor
      (itIdx, itIndices) <- getIIndices ic h t
      let cApp0 = mkApp (riC (infos !! itIdx)) itIndices
          introApp = mkApp (mkApp (Const (cdName ctor) (icLevels ic)) (hParams h)) bu
          cApp = App cApp0 introApp
      v <- forM u $ \ui -> do
        (xs, uIdx, uIndices) <- recFieldInfo ic h ui
        let cApp2 = App (mkApp (riC (infos !! uIdx)) uIndices) (mkApp ui xs)
        viTy <- mkPiFVars tc xs cApp2
        decl <- getLocalDecl tc ui
        mkLocal ic (appendAfter (ldName decl) "_ih") viTy BDefault
      inner <- mkPiFVars tc v cApp
      minorTy <- mkPiFVars tc bu inner
      let minorName = replacePrefix (cdName ctor) (itName it) anonymous
      mkLocal ic minorName minorTy BDefault
  pure (infos, minors)

recLevels :: IC -> Level -> [Level]
recLevels ic el = case el of LParam _ -> el : icLevels ic; _ -> icLevels ic

recLParams :: IC -> Level -> [Name]
recLParams ic el = case el of LParam p -> p : icLParams ic; _ -> icLParams ic

declareRecursors :: IC -> Hdr -> Level -> Bool -> [RecInfo] -> [[Expr]] -> IO ()
declareRecursors ic h elimLevel kTarget infos minorsPer = do
  tc <- withTc ic
  let cs = map riC infos
      minors = concat minorsPer
      nminors = length minors
      nmotives = length cs
      allN = map itName (icTypes ic)
      lvls = recLevels ic elimLevel
  foldM_ (\minorIdx (dIdx, it) -> do
    let info = infos !! dIdx
        cApp = App (mkApp (riC info) (riIndices info)) (riMajor info)
    t1 <- mkPiFVars tc [riMajor info] cApp
    t2 <- mkPiFVars tc (riIndices info) t1
    t3 <- mkPiFVars tc minors t2
    t4 <- mkPiFVars tc cs t3
    t5 <- mkPiFVars tc (hParams h) t4
    let recTy = inferImplicit t5 maxBound True
    -- the computation rules
    (rules, minorIdx') <- foldM (\(acc, mi) ctor -> do
      (bu, u, _) <- ctorFields ic h ctor
      v <- forM u $ \ui -> do
        (xs, itIdx, itIndices) <- recFieldInfo ic h ui
        let recName = mkRecName (itName (icTypes ic !! itIdx))
            recApp = mkApp (mkApp (mkApp (mkApp (Const recName lvls) (hParams h)) cs) minors) itIndices
        mkLambdaFVars tc xs (App recApp (mkApp ui xs))
      let eApp = mkApp (mkApp (minors !! mi) bu) v
      l1 <- mkLambdaFVars tc bu eApp
      l2 <- mkLambdaFVars tc minors l1
      l3 <- mkLambdaFVars tc cs l2
      rhs <- mkLambdaFVars tc (hParams h) l3
      pure (acc ++ [RecRule (cdName ctor) (length bu) rhs], mi + 1)) ([], minorIdx) (itCtors it)
    let recName = mkRecName (itName it)
    checkName (icEnv ic) recName
    addCore (icEnv ic) (ConstantInfo recName (recLParams ic elimLevel) recTy
      (KRec { kAll = allN, kNumParams = icNParams ic, kNumIndices = hNIndices h !! dIdx, kNumMotives = nmotives
            , kNumMinors = nminors, kRules = rules, kK = kTarget, kUnsafe = icUnsafe ic }))
    pure minorIdx') 0 (zip [0 ..] (icTypes ic))

-- | Defensive check: each recursor type is well typed and each computation rule preserves types.
checkRecursors :: IC -> Hdr -> Level -> [RecInfo] -> [[Expr]] -> IO ()
checkRecursors ic h elimLevel infos minorsPer = do
  let cs = map riC infos
      minors = concat minorsPer
  forM_ (zip [0 :: Int ..] (icTypes ic)) $ \(_, it) -> do
    let recName = mkRecName (itName it)
    recCi <- getConst (icEnv ic) recName
    tc0 <- withTc ic
    void (checkWith tc0 (ciType recCi) (recLParams ic elimLevel))
    let recPre = mkApp (mkApp (mkApp (Const recName (recLevels ic elimLevel)) (hParams h)) cs) minors
    forM_ (itCtors it) $ \ctor -> do
      (bu, _, t) <- ctorFields ic h ctor
      (_, itIndices) <- getIIndices ic h t
      let introApp = mkApp (mkApp (Const (cdName ctor) (icLevels ic)) (hParams h)) bu
          lhs = App (mkApp recPre itIndices) introApp
      tc <- withTc ic
      expected <- infer tc lhs
      reduct <- whnf tc lhs
      actual <- infer tc reduct
      ok <- isDefEq tc actual expected
      unless ok $ kerr ("generated recursor computation rule for '" ++ showN (cdName ctor) ++ "' is not type-preserving")

-- ---------------------------------------------------------------- nested inductives

data ElimRes = ElimRes
  { erParams :: [Expr]
  , erTc :: TC                              -- ^ holds the parameters' local context
  , erAux2Nested :: [(Name, Expr)]          -- ^ auxiliary type name and the nested occurrence it replaces
  , erAuxDecl :: IndDecl
  }

-- | Replace each nested occurrence @I Ds is@ (a previously declared inductive applied to parameters that mention
-- the block) by an auxiliary type @Iaux As is@ added to the block, so that the result is an ordinary mutual block.
elimNested :: Env -> IndDecl -> IO ElimRes
elimNested env d = do
  let nparams = idNumParams d
      lvls = map LParam (idLParams d)
  firstType <- case idTypes d of
    (t : _) -> pure t
    [] -> kerr "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type."
  tcP <- newTC env Safe
  (_, params) <- getParams tcP (itType firstType) nparams
  newTypes <- newIORef (idTypes d)
  nestedAux <- newIORef ([] :: [(Expr, Name)])
  nextIdx <- newIORef (1 :: Integer)
  let mkUniqueName n = do
        i <- readIORef nextIdx
        writeIORef nextIdx (i + 1)
        let r = appendIndexAfter n i
        ex <- containsConst env r
        if ex then mkUniqueName n else pure r
      replaceParams e as = instantiateRev (abstractFVars e (fvIds as)) params
      isNestedInductiveApp e = case e of
        App {} | Const fn _ <- getAppFn e -> do
          mi <- findConst env fn
          case mi of
            Just info@ConstantInfo { ciKind = KInduct { kNumParams = np } } -> do
              let args = getAppArgs e
              if np > length args then pure Nothing else do
                nts <- readIORef newTypes
                let ps = take np args
                    looseB = any hasLooseBVars ps
                    isNested = any (findE (\t _ -> case t of Const c _ -> any ((== c) . itName) nts; _ -> False)) ps
                if not isNested then pure Nothing
                else if looseB then kerr ("invalid nested inductive datatype '" ++ showN fn ++ "', nested inductive datatypes parameters cannot contain local variables.")
                else pure (Just info)
            _ -> pure Nothing
        _ -> pure Nothing
      replaceIfNested tc as e = do
        mi <- isNestedInductiveApp e
        case mi of
          Nothing -> pure Nothing
          Just iVal -> do
            let Const iName iLvls = getAppFn e
                args = getAppArgs e
                iNparams = kNumParams (ciKind iVal)
                iAs = mkApp (Const iName iLvls) (take iNparams args)
                iParams = replaceParams iAs as
            aux <- readIORef nestedAux
            case find (\(nested, _) -> nested == iParams) aux of
              Just (_, auxIName) ->
                pure (Just (mkApp (mkApp (Const auxIName lvls) as) (drop iNparams args)))
              Nothing -> do
                resRef <- newIORef Nothing
                forM_ (kAll (ciKind iVal)) $ \jName -> do
                  jInfo <- getConst env jName
                  let jAs = mkApp (Const jName iLvls) (take iNparams args)
                  auxJName <- mkUniqueName (appendName nestedPrefix jName)
                  let auxJType0 = instantiateLevelParams (ciType jInfo) (ciLParams jInfo) iLvls
                  auxJType1 <- instantiatePiParams auxJType0 (take iNparams args)
                  auxJType <- mkPiFVars tc as auxJType1
                  modifyIORef nestedAux (++ [(replaceParams jAs as, auxJName)])
                  when (jName == iName) $
                    writeIORef resRef (Just (mkApp (mkApp (Const auxJName lvls) as) (drop iNparams args)))
                  jCtors <- case ciKind jInfo of
                    KInduct { kCtors = cs } -> pure cs
                    _ -> kerr "internal error: nested inductive is not an inductive type"
                  auxCtors <- forM jCtors $ \jCtorName -> do
                    jCtorInfo <- getConst env jCtorName
                    let auxCName = replacePrefix jCtorName jName auxJName
                        t0 = instantiateLevelParams (ciType jCtorInfo) (ciLParams jCtorInfo) iLvls
                    t1 <- instantiatePiParams t0 (take iNparams args)
                    t2 <- mkPiFVars tc as t1
                    pure (CtorDecl auxCName t2)
                  modifyIORef newTypes (++ [IndType auxJName auxJType auxCtors])
                readIORef resRef >>= maybe (kerr "internal error: nested inductive replacement produced no result") (pure . Just)
      instantiatePiParams e ps = do
        let strip x [] = Just x
            strip (Pi _ _ _ b) (_ : more) = strip b more
            strip _ _ = Nothing
        case strip e ps of
          Nothing -> kerr "invalid nested inductive datatype, ill-formed declaration"
          Just b -> pure (instantiateRev b ps)
      loop q = do
        ts <- readIORef newTypes
        when (q < length ts) $ do
          let it = ts !! q
          ctors' <- forM (itCtors it) $ \c -> do
            tcC <- newTC env Safe
            (ctorType, as) <- getParams tcC (cdType c) nparams
            newT <- replaceIO (\t _ -> replaceIfNested tcC as t) ctorType
            newCtorType <- mkPiFVars tcC as newT
            pure (CtorDecl (cdName c) newCtorType)
          modifyIORef newTypes (\xs -> take q xs ++ [it { itCtors = ctors' }] ++ drop (q + 1) xs)
          loop (q + 1)
  loop 0
  ts <- readIORef newTypes
  aux <- readIORef nestedAux
  pure ElimRes { erParams = params, erTc = tcP
               , erAux2Nested = [(n, nested) | (nested, n) <- aux]
               , erAuxDecl = IndDecl (idLParams d) (idNumParams d) ts (idUnsafe d) }
  where
    fvIds = map (\case FVar i -> i; _ -> -1)

-- | Peel @n@ parameters off a Pi telescope, creating a local for each.
getParams :: TC -> Expr -> Int -> IO (Expr, [Expr])
getParams tc = go []
  where
    go acc t 0 = pure (t, reverse acc)
    go acc (Pi n bi d b) k = do
      l <- mkLocalDecl tc n d bi
      go (l : acc) (instantiate1 b l) (k - 1 :: Int)
    go _ _ _ = kerr "invalid inductive datatype declaration, incorrect number of parameters"

-- | The nested occurrence for an auxiliary constructor name, if it is one.
nestedOfAuxCtor :: Env -> ElimRes -> Name -> IO (Maybe (Expr, Name))
nestedOfAuxCtor auxEnv res c = do
  mi <- findConst auxEnv c
  pure $ case mi of
    Just ConstantInfo { ciKind = KCtor { kInduct = ind } } -> fmap (\ne -> (ne, ind)) (lookup ind (erAux2Nested res))
    _ -> Nothing

restoreConstructorName :: Env -> ElimRes -> Name -> IO Name
restoreConstructorName auxEnv res ctorName = do
  p <- nestedOfAuxCtor auxEnv res ctorName
  case p of
    Nothing -> kerr ("failed to restore nested inductive types, '" ++ showN ctorName ++ "' is not a constructor of an auxiliary type")
    Just (nested, auxName) -> case getAppFn nested of
      Const iname _ -> pure (replacePrefix ctorName auxName iname)
      _ -> kerr "failed to restore nested inductive types, nested occurrence is not an inductive type application"

-- | Rewrite auxiliary types and constructors (and renamed recursors) back to the nested originals.
restoreNestedExpr :: Env -> ElimRes -> M.Map Name Name -> Expr -> IO Expr
restoreNestedExpr auxEnv res recMap e0 = do
  let nparams = length (erParams res)
      isPi = case e0 of Pi {} -> True; _ -> False
  tcL <- newTC auxEnv Safe
  let peel acc e k
        | k == (0 :: Int) = pure (reverse acc, e)
        | otherwise = case e of
            Pi n bi d b -> next n bi d b
            Lam n bi d b -> next n bi d b
            _ -> kerr "failed to restore nested inductive types, fewer binders than parameters"
        where next n bi d b = do
                a <- mkLocalDecl tcL n d bi
                peel (a : acc) (instantiate1 b a) (k - 1)
  (as, body) <- peel [] e0 nparams
  let paramIds = map (\case FVar i -> i; _ -> -1) (erParams res)
  body' <- replaceIO (\t _ -> case t of
      Const c ls | Just rn <- M.lookup c recMap -> pure (Just (Const rn ls))
      _ -> case getAppFn t of
        Const fn _ -> case lookup fn (erAux2Nested res) of
          Just nested -> do
            let args = getAppArgs t
            when (length args < nparams) $ kerr "failed to restore nested inductive types, auxiliary type is not applied to all parameters"
            let newT = instantiateRev (abstractFVars nested paramIds) as
            pure (Just (mkApp newT (drop nparams args)))
          Nothing -> do
            m <- nestedOfAuxCtor auxEnv res fn
            case m of
              Just (nested2, auxIName) -> do
                let args = getAppArgs t
                when (length args < nparams) $ kerr "failed to restore nested inductive types, auxiliary constructor is not applied to all parameters"
                let newNested = instantiateRev (abstractFVars nested2 paramIds) as
                case getAppFn newNested of
                  Const iname ils -> do
                    let newFnName = replacePrefix fn auxIName iname
                        newFn = Const newFnName ils
                    pure (Just (mkApp (mkApp newFn (getAppArgs newNested)) (drop nparams args)))
                  _ -> kerr "failed to restore nested inductive types, nested occurrence is not an inductive type application"
              Nothing -> pure Nothing
        _ -> pure Nothing) body
  mkBinding' tcL (not isPi) as body'
  where
    mkBinding' tcL isLam as b = if isLam then mkLambdaFVars tcL as b else mkPiFVars tcL as b

mkAuxRecNameMap :: Env -> IndDecl -> IO ([Name], M.Map Name Name)
mkAuxRecNameMap auxEnv d = do
  let ntypes = length (idTypes d)
  mainName <- case idTypes d of
    (t : _) -> pure (itName t)
    [] -> kerr "invalid empty inductive declaration"
  mainInfo <- getConst auxEnv mainName
  let allN = kAll (ciKind mainInfo)
      aux = drop ntypes allN
      pairs = [ (mkRecName ind, appendIndexAfter (mkRecName mainName) i) | (ind, i) <- zip aux [1 ..] ]
  pure (map fst pairs, M.fromList pairs)

restoreNested :: Env -> Env -> IndDecl -> ElimRes -> IO ()
restoreNested env auxEnv d res = do
  let allIndNames = map itName (idTypes d)
      safety = if idUnsafe d then Unsafe else Safe
  (auxRecNames, recMap) <- mkAuxRecNameMap auxEnv d
  newRecNames <- newIORef []
  let processRec recName = do
        let newRecName = fromMaybe recName (M.lookup recName recMap)
        recInfo <- getConst auxEnv recName
        newRecType <- restoreNestedExpr auxEnv res recMap (ciType recInfo)
        let KRec { kRules = rules, kNumParams = np, kNumIndices = ni, kNumMotives = nm, kNumMinors = nmin, kK = k, kUnsafe = u } = ciKind recInfo
        newRules <- forM rules $ \rule -> do
          newRhs <- restoreNestedExpr auxEnv res recMap (rrRhs rule)
          newCtor <- if newRecName /= recName then restoreConstructorName auxEnv res (rrCtor rule) else pure (rrCtor rule)
          pure (RecRule newCtor (rrNumFields rule) newRhs)
        checkName env newRecName
        addCore env (ConstantInfo newRecName (ciLParams recInfo) newRecType
          (KRec { kAll = allIndNames, kNumParams = np, kNumIndices = ni, kNumMotives = nm, kNumMinors = nmin
                , kRules = newRules, kK = k, kUnsafe = u }))
        modifyIORef newRecNames (++ [newRecName])
  forM_ (idTypes d) $ \it -> do
    indVal <- getConst auxEnv (itName it)
    checkName env (ciName indVal)
    let k@KInduct { kCtors = ctors } = ciKind indVal
    addCore env indVal { ciKind = k { kAll = allIndNames } }
    forM_ ctors $ \cn -> do
      ctorVal <- getConst auxEnv cn
      newType <- restoreNestedExpr auxEnv res M.empty (ciType ctorVal)
      checkName env (ciName ctorVal)
      addCore env ctorVal { ciType = newType }
    processRec (mkRecName (itName it))
  mapM_ processRec auxRecNames
  -- the parametric arguments of the nested occurrences were not part of the auxiliary declaration: check them now
  tcN <- newTCWith env (tcLctx (erTc res)) safety False True
  forM_ (map snd (erAux2Nested res)) $ \nested -> checkWith tcN nested (idLParams d)
  -- re-check everything the restoration rewrote
  tc <- newTC env safety
  forM_ (idTypes d) $ \it -> forM_ (itCtors it) $ \c -> do
    ci <- getConst env (cdName c)
    checkWith tc (ciType ci) (idLParams d)
  names <- readIORef newRecNames
  forM_ names $ \rn -> do
    ri <- getConst env rn
    void (checkWith tc (ciType ri) (ciLParams ri))
    case ciKind ri of
      KRec { kRules = rs } -> forM_ rs $ \r -> checkWith tc (rrRhs r) (ciLParams ri)
      _ -> pure ()
