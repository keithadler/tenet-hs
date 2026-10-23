{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | Checking a declaration and adding the resulting constants to an environment.
module Tenet.Add (addDecl) where

import Control.Exception
import Control.Monad
import Tenet.Env
import Tenet.Expr
import Tenet.Inductive
import Tenet.Name
import Tenet.Quot
import Tenet.TypeChecker

-- | Check a declaration and add its constants. A rejection leaves the environment unchanged. The first attempt
-- caches failed equalities, which can only reject more; a rejected declaration is then re-checked with the
-- reference algorithm, so the verdict reported is exactly the reference's.
addDecl :: Env -> Declaration -> IO ()
addDecl env d = do
  snap <- snapshotEnv env
  r <- try (addCoreDecl env d `catch` outOfStack)
  case r of
    Right () -> pure ()
    Left ex -> do
      restoreEnv env snap
      case ex of
        KernelError _ -> do
          r2 <- try (withFaithful (addCoreDecl env d))
          case r2 of
            Right () -> pure ()
            Left ex2 -> restoreEnv env snap >> throwIO (ex2 :: KernelError)
        _ -> throwIO ex

-- | A term nested deeply enough to exhaust the stack makes GHC raise 'StackOverflow', which would otherwise end the
-- whole run with an uncaught exception. It is reported like any other undecided declaration: the checker neither
-- accepts it nor claims it is wrong, and the environment is restored, so the rest of the export is still checked.
outOfStack :: AsyncException -> IO a
outOfStack StackOverflow =
  throwIO (Unsupported "expression too deep: ran out of stack while reducing or traversing a term")
outOfStack e = throwIO e

-- | The namespace nested-inductive elimination generates its auxiliary types into. Lean reserves it against
-- ordinary declarations; the kernel's own auxiliaries are installed with 'addCore', so reserving it costs a
-- legitimate file nothing.
nestedPrefix :: Name
nestedPrefix = nameOf ["_nested"]

addCoreDecl :: Env -> Declaration -> IO ()
addCoreDecl env d = do
  forM_ (declNames d) $ \n ->
    when (nestedPrefix `isPrefixOf` n) $
      kerr ("invalid declaration '" ++ showName n ++ "': '" ++ showName nestedPrefix
            ++ "' is reserved for the auxiliary types the kernel derives when eliminating a nested inductive, "
            ++ "and a declaration may not occupy that namespace")
  case d of
    DAxiom n lps ty unsafe -> do
      tc <- newTC env (if unsafe then Unsafe else Safe)
      checkConstantVal env n lps ty tc
      addCore env (ConstantInfo n lps ty (KAxiom unsafe))
    DDef def -> addDefinition env def
    DThm n lps ty val allN -> do
      tc <- newTC env Safe
      checkConstantVal env n lps ty tc
      p <- isProp tc ty
      unless p $ kerr ("type of theorem '" ++ showName n ++ "' is not a proposition: " ++ showExpr ty)
      checkValue tc n lps ty val
      addCore env (ConstantInfo n lps ty (KThm val allN))
    DOpaque n lps ty val unsafe allN -> do
      -- the reference checks opaque values with a safe checker regardless of the unsafe flag
      tc <- newTC env Safe
      checkConstantVal env n lps ty tc
      checkValue tc n lps ty val
      addCore env (ConstantInfo n lps ty (KOpaque val unsafe allN))
    DMutual defs -> addMutual env defs
    DQuot -> addQuot env
    DInductive ind -> addInductive env ind

checkNoFVarE :: Name -> Expr -> IO ()
checkNoFVarE n e = when (hasFVar e) $ kerr ("declaration '" ++ showName n ++ "' contains free variables")

checkConstantVal :: Env -> Name -> [Name] -> Expr -> TC -> IO ()
checkConstantVal env n lps ty tc = do
  checkName env n
  checkDuplicatedUnivParams lps
  checkNoFVarE n ty
  sort <- checkWith tc ty lps
  void (ensureSort tc sort)

checkValue :: TC -> Name -> [Name] -> Expr -> Expr -> IO ()
checkValue tc n lps ty val = do
  checkNoFVarE n val
  valType <- checkWith tc val lps
  ok <- isDefEq tc valType ty
  unless ok $ kerr ("declaration type mismatch for '" ++ showName n ++ "'\n  expected: " ++ showExpr ty ++ "\n  inferred: " ++ showExpr valType)

defInfo :: DefDecl -> ConstantInfo
defInfo d = ConstantInfo (dName d) (dLParams d) (dType d) (KDef (dValue d) (dHints d) (dSafety d) (dAll d))

addDefinition :: Env -> DefDecl -> IO ()
addDefinition env d
  | dSafety d == Unsafe = do
      -- unsafe definitions may be recursive: check the header, add, then check the body
      tc1 <- newTC env Unsafe
      checkConstantVal env (dName d) (dLParams d) (dType d) tc1
      addCore env (defInfo d)
      tc2 <- newTC env Unsafe
      checkValue tc2 (dName d) (dLParams d) (dType d) (dValue d)
  | otherwise = do
      -- safe and partial definitions are checked with a safe checker: a partial definition may not depend on another
      tc <- newTC env Safe
      checkConstantVal env (dName d) (dLParams d) (dType d) tc
      checkValue tc (dName d) (dLParams d) (dType d) (dValue d)
      addCore env (defInfo d)

addMutual :: Env -> [DefDecl] -> IO ()
addMutual _ [] = kerr "invalid empty mutual definition"
addMutual env defs@(d0 : _) = do
  let safety = dSafety d0
      lps = dLParams d0
  when (safety == Safe) $ kerr "invalid mutual definition, declaration is not tagged as unsafe/partial"
  tc <- newTC env safety
  foldM_ (\found v -> do
    when (dSafety v /= safety) $ kerr "invalid mutual definition, declarations must have the same safety annotation"
    when (dLParams v /= lps) $ kerr "invalid mutual definition, declarations must have the same universe level parameters"
    when (dName v `elem` found) $ kerr ("invalid mutual definition, duplicate declaration name '" ++ showName (dName v) ++ "'")
    checkConstantVal env (dName v) (dLParams v) (dType v) tc
    pure (dName v : found)) [] defs
  mapM_ (addCore env . defInfo) defs
  tc2 <- newTC env safety
  forM_ defs $ \v -> checkValue tc2 (dName v) (dLParams v) (dType v) (dValue v)
