{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Constants, declarations, and the environment of checked constants.
module Tenet.Env
  ( KernelError (..), kerr, unsupported
  , Hints (..), compareHints, Safety (..), QuotKind (..), RecRule (..)
  , ConstantInfo (..), ConstKind (..)
  , ciValue, ciIsUnsafe, ciKindName, ciHints
  , recMajorIdx, recMajorInduct, recRuleFor
  , Declaration (..), DefDecl (..), IndDecl (..), IndType (..), CtorDecl (..), declNames
  , Options (..), defaultOptions
  , Env (..), EnvData (..), Primitive (..)
  , kernelHasNoNativeReduction
  , newEnv, childEnv, findConst, getConst, containsConst, addCore, quotInitialized, markQuotInitialized
  , snapshotEnv, restoreEnv, ownConstants, envSize, checkName, checkDuplicatedUnivParams, stringLiteralConstructor
  ) where

import Control.Exception
import Control.Monad (forM_, when)
import Data.Char (isDigit, isSpace, toLower)
import Data.IORef
import qualified Data.List as L
import qualified Data.Map.Strict as M
import Tenet.Expr
import Tenet.Name

-- | A rejection by the kernel. 'Unsupported' is a declaration the checker will not decide, such as
-- one that needs compiled code; 'Timeout' is the deterministic work bound.
data KernelError
  = KernelError String
  | Unsupported String
  | Timeout Int
  deriving (Show)

instance Exception KernelError

kerr :: String -> IO a
kerr = throwIO . KernelError

unsupported :: String -> IO a
unsupported = throwIO . Unsupported

data Hints = HOpaque | HAbbrev | HRegular !Int
  deriving (Eq, Show)

-- | Negative: unfold the first; positive: unfold the second; zero: unfold both.
compareHints :: Hints -> Hints -> Int
compareHints (HRegular a) (HRegular b)
  | a == b = 0
  | a > b = -1
  | otherwise = 1
compareHints h1 h2
  | sameKind h1 h2 = 0
  | h1 == HOpaque = 1
  | h2 == HOpaque = -1
  | h1 == HAbbrev = -1
  | otherwise = 1
  where
    sameKind HOpaque HOpaque = True
    sameKind HAbbrev HAbbrev = True
    sameKind (HRegular _) (HRegular _) = True
    sameKind _ _ = False

data Safety = Unsafe | Safe | Partial
  deriving (Eq, Show)

data QuotKind = QType | QCtor | QLift | QInd
  deriving (Eq, Show)

data RecRule = RecRule { rrCtor :: !Name, rrNumFields :: !Int, rrRhs :: !Expr }

data ConstKind
  = KAxiom { kUnsafe :: !Bool }
  | KDef { kValue :: !Expr, kHints :: !Hints, kSafety :: !Safety, kAll :: [Name] }
  | KThm { kValue :: !Expr, kAll :: [Name] }
  | KOpaque { kValue :: !Expr, kUnsafe :: !Bool, kAll :: [Name] }
  | KQuot { kQuot :: !QuotKind }
  | KInduct { kNumParams :: !Int, kNumIndices :: !Int, kAll :: [Name], kCtors :: [Name], kNumNested :: !Int
            , kIsRec :: !Bool, kUnsafe :: !Bool, kReflexive :: !Bool }
  | KCtor { kInduct :: !Name, kCidx :: !Int, kNumParams :: !Int, kNumFields :: !Int, kUnsafe :: !Bool }
  | KRec { kAll :: [Name], kNumParams :: !Int, kNumIndices :: !Int, kNumMotives :: !Int, kNumMinors :: !Int
         , kRules :: [RecRule], kK :: !Bool, kUnsafe :: !Bool }

data ConstantInfo = ConstantInfo
  { ciName :: !Name
  , ciLParams :: [Name]
  , ciType :: !Expr
  , ciKind :: !ConstKind
  }

-- | The value the kernel may unfold: definitions and theorems. Opaque constants are never unfolded.
ciValue :: ConstantInfo -> Maybe Expr
ciValue c = case ciKind c of
  KDef { kValue = v } -> Just v
  KThm { kValue = v } -> Just v
  _ -> Nothing

ciHints :: ConstantInfo -> Hints
ciHints c = case ciKind c of
  KDef { kHints = h } -> h
  _ -> HOpaque

ciIsUnsafe :: ConstantInfo -> Bool
ciIsUnsafe c = case ciKind c of
  KAxiom u -> u
  KDef { kSafety = s } -> s == Unsafe
  KOpaque { kUnsafe = u } -> u
  KInduct { kUnsafe = u } -> u
  KCtor { kUnsafe = u } -> u
  KRec { kUnsafe = u } -> u
  _ -> False

ciKindName :: ConstantInfo -> String
ciKindName c = case ciKind c of
  KAxiom {} -> "axiom"
  KDef {} -> "def"
  KThm {} -> "theorem"
  KOpaque {} -> "opaque"
  KQuot {} -> "quot"
  KInduct {} -> "inductive"
  KCtor {} -> "constructor"
  KRec {} -> "recursor"

-- | Index of the major premise among a recursor's arguments.
recMajorIdx :: ConstantInfo -> Int
recMajorIdx c = case ciKind c of
  KRec { kNumParams = p, kNumMotives = m, kNumMinors = n, kNumIndices = i } -> p + m + n + i
  _ -> 0

-- | The inductive type of the major premise, read off the recursor's type. Like the reference, this walks
-- lambdas as well as pis.
recMajorInduct :: ConstantInfo -> IO Name
recMajorInduct c = go (recMajorIdx c) (ciType c)
  where
    bad = kerr ("malformed recursor type for '" ++ showName (ciName c) ++ "'")
    body (Pi _ _ _ b) = Just b
    body (Lam _ _ _ b) = Just b
    body _ = Nothing
    dom (Pi _ _ d _) = Just d
    dom (Lam _ _ d _) = Just d
    dom _ = Nothing
    go 0 e = case dom e of
      Just d | Const n _ <- getAppFn d -> pure n
      _ -> bad
    go k e = maybe bad (go (k - 1 :: Int)) (body e)

recRuleFor :: ConstantInfo -> Expr -> Maybe RecRule
recRuleFor c major = case (ciKind c, getAppFn major) of
  (KRec { kRules = rs }, Const n _) -> case filter ((== n) . rrCtor) rs of
    (r : _) -> Just r
    [] -> Nothing
  _ -> Nothing

-- ---------------------------------------------------------------- declarations (input to checking)

data DefDecl = DefDecl
  { dName :: Name, dLParams :: [Name], dType :: Expr, dValue :: Expr
  , dHints :: Hints, dSafety :: Safety, dAll :: [Name] }

data CtorDecl = CtorDecl { cdName :: Name, cdType :: Expr }

data IndType = IndType { itName :: Name, itType :: Expr, itCtors :: [CtorDecl] }

data IndDecl = IndDecl { idLParams :: [Name], idNumParams :: Int, idTypes :: [IndType], idUnsafe :: Bool }

data Declaration
  = DAxiom Name [Name] Expr Bool
  | DDef DefDecl
  | DThm Name [Name] Expr Expr [Name]
  | DOpaque Name [Name] Expr Expr Bool [Name]
  | DMutual [DefDecl]
  | DQuot
  | DInductive IndDecl

declNames :: Declaration -> [Name]
declNames = \case
  DAxiom n _ _ _ -> [n]
  DDef d -> [dName d]
  DThm n _ _ _ _ -> [n]
  DOpaque n _ _ _ _ _ -> [n]
  DMutual ds -> map dName ds
  DQuot -> []
  DInductive d -> concatMap (\t -> itName t : map cdName (itCtors t)) (idTypes d)

-- ---------------------------------------------------------------- environment

data Options = Options
  { optPrimitiveCheck :: !Bool   -- ^ validate the Nat/String primitives before taking their shortcuts
  , optMaxUnfolds :: !Int        -- ^ deterministic work bound, in definition unfoldings per checker
  , optCompareInductive :: !Bool
  }

defaultOptions :: Options
defaultOptions = Options { optPrimitiveCheck = True, optMaxUnfolds = 100000000, optCompareInductive = True }

-- | Whether Lean's own kernel of this version does not evaluate @Lean.reduceBool@ and @Lean.reduceNat@. Lean 4.34 and
-- earlier did (running compiled code); it was removed before 4.35.0-rc1, so from 4.35 on a term such as
-- @Lean.reduceBool b@ is an ordinary stuck constant application and a proof that needs it is a type mismatch. An
-- unparsable version, or a nightly build, answers 'False': the checker then keeps declining those terms instead of
-- guessing that a kernel it cannot identify rejects them.
kernelHasNoNativeReduction :: String -> Bool
kernelHasNoNativeReduction v0 =
  let v = dropWhile (== 'v') (dropWhile isSpace v0)
      (a, r1) = span isDigit v
      (b, r2) = span isDigit (drop 1 r1)
      (c, r3) = span isDigit (drop 1 r2)
      shaped = not (null a) && not (null b) && not (null c) && take 1 r1 == "." && take 1 r2 == "." && (null r3 || take 1 r3 == "-")
      nightly = "nightly" `L.isPrefixOf` map toLower (drop 1 r3)
      major = read a :: Integer
      minor = read b :: Integer
  in shaped && not nightly && (major > 4 || (major == 4 && minor >= 35))

data Primitive
  = PNatLiteralType | PStringLiteralType
  | PNatSucc | PNatPred | PNatAdd | PNatSub | PNatMul | PNatPow | PNatBeq | PNatBle
  | PNatDiv | PNatMod | PNatGcd | PNatLand | PNatLor | PNatXor | PNatShiftLeft | PNatShiftRight
  deriving (Eq, Ord, Show, Enum, Bounded)

data EnvData = EnvData
  { edConsts :: !(M.Map Name ConstantInfo)
  , edOwn :: [ConstantInfo]       -- ^ constants added to this environment, newest first
  , edQuot :: !Bool
  }

data Env = Env
  { envData :: IORef EnvData
  , envPrims :: IORef (M.Map Primitive Bool)
  , envOpts :: Options
  , envNativeRemoved :: IORef Bool
    -- ^ the Lean that wrote the export has no in-kernel native reduction (see 'kernelHasNoNativeReduction')
  }

newEnv :: Options -> IO Env
newEnv opts = do
  d <- newIORef (EnvData M.empty [] False)
  p <- newIORef M.empty
  n <- newIORef False
  pure (Env d p opts n)

-- | A snapshot that new constants can be layered onto without touching the parent. The listed constants are
-- hidden, so a declaration the parent already has can be re-derived and checked as if it were new.
childEnv :: Env -> [Name] -> IO Env
childEnv env hidden = do
  EnvData cs _ q <- readIORef (envData env)
  let cs' = foldr M.delete cs hidden
      q' = q && not (any (`elem` hidden) quotNames)
  d <- newIORef (EnvData cs' [] q')
  p <- newIORef M.empty
  n <- readIORef (envNativeRemoved env) >>= newIORef
  pure (Env d p (envOpts env) n)
  where
    quotNames = [nameOf ["Quot"]]

findConst :: Env -> Name -> IO (Maybe ConstantInfo)
findConst env n = M.lookup n . edConsts <$> readIORef (envData env)

getConst :: Env -> Name -> IO ConstantInfo
getConst env n = findConst env n >>= maybe (kerr ("unknown constant '" ++ showName n ++ "'")) pure

containsConst :: Env -> Name -> IO Bool
containsConst env n = maybe False (const True) <$> findConst env n

-- | Add a constant without checking it. Reserved for constants the kernel derived itself.
addCore :: Env -> ConstantInfo -> IO ()
addCore env c = modifyIORef' (envData env) $ \d ->
  d { edConsts = M.insert (ciName c) c (edConsts d), edOwn = c : edOwn d }

quotInitialized :: Env -> IO Bool
quotInitialized env = edQuot <$> readIORef (envData env)

markQuotInitialized :: Env -> IO ()
markQuotInitialized env = modifyIORef' (envData env) (\d -> d { edQuot = True })

-- | Constants added to this environment (not the parent's), in order of addition.
ownConstants :: Env -> IO [ConstantInfo]
ownConstants env = reverse . edOwn <$> readIORef (envData env)

envSize :: Env -> IO Int
envSize env = M.size . edConsts <$> readIORef (envData env)

checkName :: Env -> Name -> IO ()
checkName env n = do
  b <- containsConst env n
  when b $ kerr ("'" ++ showName n ++ "' has already been declared")

checkDuplicatedUnivParams :: [Name] -> IO ()
checkDuplicatedUnivParams ls =
  forM_ (zip [0 :: Int ..] ls) $ \(i, l) ->
    when (l `elem` drop (i + 1) ls) $
      kerr ("failed to add declaration to environment, duplicate universe level parameter: '" ++ showName l ++ "'")

-- | The constant a string literal expands to: @String.ofList@ on current Lean, @String.mk@ before.
stringLiteralConstructor :: Env -> IO Name
stringLiteralConstructor env = do
  b <- containsConst env (nameOf ["String", "ofList"])
  pure (if b then nameOf ["String", "ofList"] else nameOf ["String", "mk"])

-- | Capture and restore the environment's contents, so a rejected declaration leaves it unchanged.
snapshotEnv :: Env -> IO EnvData
snapshotEnv env = readIORef (envData env)

restoreEnv :: Env -> EnvData -> IO ()
restoreEnv env = writeIORef (envData env)
