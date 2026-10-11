{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Replaying an export: check every declaration in order and report what cannot be accepted.
module Tenet.Check
  ( CheckOptions (..), defaultCheckOptions, Failure (..), Report (..), checkFile, checkLines
  ) where

import Control.Exception
import Control.Monad
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.ByteString.Lazy.Char8 as BLC
import Data.IORef
import Data.List (intercalate)
import qualified Data.Set as S
import GHC.Clock (getMonotonicTime)
import Tenet.Add
import Tenet.Env
import Tenet.Export
import Tenet.Expr
import Tenet.Name
import Tenet.TypeChecker (unvalidatedPrimitives)

data CheckOptions = CheckOptions
  { coFailFast :: Bool
  , coQuiet :: Bool
  , coOnly :: Maybe [String]      -- ^ check just these declarations; add everything else unchecked
  , coCompareInductive :: Bool
  , coPrimitiveCheck :: Bool
  , coMaxUnfolds :: Int
  }

defaultCheckOptions :: CheckOptions
defaultCheckOptions = CheckOptions
  { coFailFast = False, coQuiet = False, coOnly = Nothing, coCompareInductive = True
  , coPrimitiveCheck = True, coMaxUnfolds = 100000000 }

data Failure = Failure { fKind :: String, fName :: Name, fSeconds :: Double, fMessage :: String }

data Report = Report
  { rChecked :: Int            -- ^ declarations accepted
  , rConstants :: Int          -- ^ constants in the environment at the end
  , rFailures :: [Failure]
  , rUnvalidated :: [Primitive]
  , rSeconds :: Double
  , rMeta :: Maybe ExportMeta
  , rFormatError :: Maybe String
  }

checkFile :: CheckOptions -> FilePath -> IO Report
checkFile opts path = do
  contents <- BL.readFile path
  checkLines opts (map BL.toStrict (BLC.lines contents))

checkLines :: CheckOptions -> [B.ByteString] -> IO Report
checkLines opts ls = do
  t0 <- getMonotonicTime
  env <- newEnv defaultOptions { optPrimitiveCheck = coPrimitiveCheck opts, optMaxUnfolds = coMaxUnfolds opts }
  failures <- newIORef []
  checked <- newIORef (0 :: Int)
  meta <- newIORef Nothing
  fmtErr <- newIORef Nothing
  let only = fmap S.fromList (coOnly opts)
      selected d = case only of
        Nothing -> True
        Just s -> any (\n -> S.member (showName n) s) (exportDeclNames d)
      loop _ [] = pure ()
      loop (lineNo :: Int, tbl) (l : rest)
        | B.null l = loop (lineNo + 1, tbl) rest
        | otherwise = case parseLine tbl l of
            Left e -> writeIORef fmtErr (Just ("line " ++ show (lineNo + 1) ++ ": " ++ e))
            Right (LMeta m) -> writeIORef meta (Just m) >> loop (lineNo + 1, tbl) rest
            Right (LTable tbl') -> loop (lineNo + 1, tbl') rest
            Right (LDecl d) -> do
              stop <- if selected d then checkOne d else installUnchecked env d >> pure False
              unless stop $ loop (lineNo + 1, tbl) rest
      checkOne d = do
        t1 <- getMonotonicTime
        r <- try (checkDecl env opts d)
        t2 <- getMonotonicTime
        case r of
          Right () -> modifyIORef' checked (+ 1) >> pure False
          Left ex -> do
            let (kind, n) = exportDeclDisplay d
                msg = case ex of
                  KernelError m -> m
                  Unsupported m -> "unsupported: " ++ m
                  Timeout k -> "deterministic timeout after " ++ show k ++ " unfoldings"
                f = Failure kind n (t2 - t1) msg
            modifyIORef' failures (f :)
            putStrLn ("FAIL " ++ kind ++ " " ++ showName n ++ " (" ++ show2 (t2 - t1) ++ "s)"
                      ++ (if coQuiet opts then "" else "\n    " ++ indent msg))
            if coFailFast opts then pure True else installUnchecked env d >> pure False
  loop (0, emptyTables) ls
  t3 <- getMonotonicTime
  fs <- reverse <$> readIORef failures
  c <- readIORef checked
  m <- readIORef meta
  fe <- readIORef fmtErr
  n <- envSize env
  unv <- unvalidatedPrimitives env
  pure Report { rChecked = c, rConstants = n, rFailures = fs, rUnvalidated = unv, rSeconds = t3 - t0, rMeta = m, rFormatError = fe }
  where
    indent = intercalate "\n    " . lines
    show2 :: Double -> String
    show2 x = show (fromIntegral (round (x * 100) :: Int) / 100 :: Double)

-- | Check one exported declaration, and for inductive and quotient blocks compare the exporter's claims.
checkDecl :: Env -> CheckOptions -> ExportDecl -> IO ()
checkDecl env opts d = do
  decl <- either (throwIO . KernelError) pure (exportDeclToDeclaration d)
  addDecl env decl
  case d of
    XQuot {} -> compareQuot env d
    XInductive {} | coCompareInductive opts -> compareInductive env d
    _ -> pure ()

require :: Bool -> Name -> String -> String -> String -> IO ()
require ok n field exported derived =
  unless ok $ kerr ("'" ++ showName n ++ "': exported " ++ field ++ " does not match the kernel's\n  exported: " ++ exported ++ "\n  kernel:   " ++ derived)

showNames :: [Name] -> String
showNames ns = "[" ++ intercalate ", " (map showName ns) ++ "]"

compareQuot :: Env -> ExportDecl -> IO ()
compareQuot env (XQuot n lps ty kind) = do
  info <- getConst env n
  case ciKind info of
    KQuot k -> do
      require (k == kind) n "quotient kind" (show kind) (show k)
      require (ciLParams info == lps) n "universe parameters" (showNames lps) (showNames (ciLParams info))
      require (ciType info == ty) n "type" (showExpr ty) (showExpr (ciType info))
    _ -> kerr ("'" ++ showName n ++ "' is not a quotient constant in the kernel's environment")
compareQuot _ _ = pure ()

-- | The exporter's metadata must agree with what the kernel derived, field by field.
compareInductive :: Env -> ExportDecl -> IO ()
compareInductive env (XInductive tys cts rcs) = do
  forM_ tys $ \t -> do
    let n = xiName t
    k <- getConst env n
    case ciKind k of
      KInduct { kNumParams = np, kNumIndices = ni, kAll = al, kCtors = cs, kNumNested = nn, kIsRec = ir, kUnsafe = un, kReflexive = rf } -> do
        require (ciLParams k == xiLParams t) n "universe parameters" (showNames (xiLParams t)) (showNames (ciLParams k))
        require (ciType k == xiType t) n "type" (showExpr (xiType t)) (showExpr (ciType k))
        require (np == xiNumParams t) n "numParams" (show (xiNumParams t)) (show np)
        require (ni == xiNumIndices t) n "numIndices" (show (xiNumIndices t)) (show ni)
        require (al == xiAll t) n "all" (showNames (xiAll t)) (showNames al)
        require (cs == xiCtors t) n "ctors" (showNames (xiCtors t)) (showNames cs)
        require (nn == xiNumNested t) n "numNested" (show (xiNumNested t)) (show nn)
        require (ir == xiIsRec t) n "isRec" (show (xiIsRec t)) (show ir)
        require (un == xiIsUnsafe t) n "isUnsafe" (show (xiIsUnsafe t)) (show un)
        require (rf == xiIsReflexive t) n "isReflexive" (show (xiIsReflexive t)) (show rf)
      _ -> kerr ("'" ++ showName n ++ "' is not an inductive type in the kernel's environment")
  forM_ cts $ \c -> do
    let n = xcName c
    k <- getConst env n
    case ciKind k of
      KCtor { kInduct = ind, kCidx = ci, kNumParams = np, kNumFields = nf, kUnsafe = un } -> do
        require (ciLParams k == xcLParams c) n "universe parameters" (showNames (xcLParams c)) (showNames (ciLParams k))
        require (ciType k == xcType c) n "type" (showExpr (xcType c)) (showExpr (ciType k))
        require (ind == xcInduct c) n "induct" (showName (xcInduct c)) (showName ind)
        require (ci == xcCidx c) n "cidx" (show (xcCidx c)) (show ci)
        require (np == xcNumParams c) n "numParams" (show (xcNumParams c)) (show np)
        require (nf == xcNumFields c) n "numFields" (show (xcNumFields c)) (show nf)
        require (un == xcIsUnsafe c) n "isUnsafe" (show (xcIsUnsafe c)) (show un)
      _ -> kerr ("'" ++ showName n ++ "' is not a constructor in the kernel's environment")
  forM_ rcs $ \r -> do
    let n = xrName r
    k <- getConst env n
    case ciKind k of
      KRec { kAll = al, kNumParams = np, kNumIndices = ni, kNumMotives = nm, kNumMinors = nmin, kRules = rules, kK = kk, kUnsafe = un } -> do
        require (ciLParams k == xrLParams r) n "universe parameters" (showNames (xrLParams r)) (showNames (ciLParams k))
        require (ciType k == xrType r) n "type" (showExpr (xrType r)) (showExpr (ciType k))
        require (al == xrAll r) n "all" (showNames (xrAll r)) (showNames al)
        require (np == xrNumParams r) n "numParams" (show (xrNumParams r)) (show np)
        require (ni == xrNumIndices r) n "numIndices" (show (xrNumIndices r)) (show ni)
        require (nm == xrNumMotives r) n "numMotives" (show (xrNumMotives r)) (show nm)
        require (nmin == xrNumMinors r) n "numMinors" (show (xrNumMinors r)) (show nmin)
        require (kk == xrK r) n "k" (show (xrK r)) (show kk)
        require (un == xrIsUnsafe r) n "isUnsafe" (show (xrIsUnsafe r)) (show un)
        require (length rules == length (xrRules r)) n "number of rules" (show (length (xrRules r))) (show (length rules))
        forM_ (zip3 [0 :: Int ..] (xrRules r) rules) $ \(i, er, kr) -> do
          require (rrCtor kr == xrCtor er) n ("rule " ++ show i ++ " constructor") (showName (xrCtor er)) (showName (rrCtor kr))
          require (rrNumFields kr == xrNumFields er) n ("rule " ++ show i ++ " nfields") (show (xrNumFields er)) (show (rrNumFields kr))
          require (rrRhs kr == xrRhs er) n ("rule " ++ show i ++ " rhs") (showExpr (xrRhs er)) (showExpr (rrRhs kr))
      _ -> kerr ("'" ++ showName n ++ "' is not a recursor in the kernel's environment")
  -- the kernel must not have produced constants the exporter does not know about, or the reverse
  let exported = map xiName tys ++ map xcName cts ++ map xrName rcs
  forM_ (concatMap xiAll tys) $ \n -> do
    unless (n `elem` exported) $ do
      m <- findConst env n
      case m of
        Just ConstantInfo { ciKind = KInduct {} } ->
          kerr ("'" ++ maybe "?" (showName . xiName) (safeHead tys) ++ "': the block's 'all' field names '" ++ showName n ++ "', which the export does not define")
        _ -> pure ()
  where
    safeHead (x : _) = Just x
    safeHead [] = Nothing
compareInductive _ _ = pure ()

-- | Install the exporter's own view of a declaration without checking it, so later declarations can still be
-- checked after a failure. Constants that are already present are left alone.
installUnchecked :: Env -> ExportDecl -> IO ()
installUnchecked env = \case
  XAxiom n lps ty u -> add (ConstantInfo n lps ty (KAxiom u))
  XDef d -> addDef d
  XMutual ds -> mapM_ addDef ds
  XThm n lps ty v a -> add (ConstantInfo n lps ty (KThm v a))
  XOpaque n lps ty v u a -> add (ConstantInfo n lps ty (KOpaque v u a))
  XQuot n lps ty k -> do
    add (ConstantInfo n lps ty (KQuot k))
    when (k == QInd) (markQuotInitialized env)
  XInductive tys cts rcs -> do
    forM_ tys $ \t -> add (ConstantInfo (xiName t) (xiLParams t) (xiType t)
      (KInduct (xiNumParams t) (xiNumIndices t) (xiAll t) (xiCtors t) (xiNumNested t) (xiIsRec t) (xiIsUnsafe t) (xiIsReflexive t)))
    forM_ cts $ \c -> add (ConstantInfo (xcName c) (xcLParams c) (xcType c)
      (KCtor (xcInduct c) (xcCidx c) (xcNumParams c) (xcNumFields c) (xcIsUnsafe c)))
    forM_ rcs $ \r -> add (ConstantInfo (xrName r) (xrLParams r) (xrType r)
      (KRec (xrAll r) (xrNumParams r) (xrNumIndices r) (xrNumMotives r) (xrNumMinors r)
            [RecRule (xrCtor x) (xrNumFields x) (xrRhs x) | x <- xrRules r] (xrK r) (xrIsUnsafe r)))
  where
    addDef d = add (ConstantInfo (dName d) (dLParams d) (dType d) (KDef (dValue d) (dHints d) (dSafety d) (dAll d)))
    add c = do
      present <- containsConst env (ciName c)
      unless present (addCore env c)
