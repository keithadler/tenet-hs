{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
module Main (main) where

import Control.Monad
import qualified Data.ByteString as B
import Data.IORef
import Data.List (sort)
import qualified Data.Text as T
import System.Directory (getTemporaryDirectory, listDirectory, removeFile)
import System.Exit
import System.FilePath ((</>), takeExtension)
import Tenet.Check
import Tenet.Expr
import Tenet.ExprOps
import Tenet.Json
import Tenet.Level
import Tenet.Name

fixtures :: FilePath
fixtures = "tests/fixtures"

main :: IO ()
main = do
  failures <- newIORef (0 :: Int)
  total <- newIORef (0 :: Int)
  let test name ok = do
        modifyIORef' total (+ 1)
        unless ok $ do
          modifyIORef' failures (+ 1)
          putStrLn ("FAIL: " ++ name)

  -- levels
  let u = LParam (nameStr "u")
      v = LParam (nameStr "v")
  test "max is commutative" (isEquiv (LMax u v) (LMax v u))
  test "imax u (succ v) = max u (succ v)" (isEquiv (LIMax u (LSucc v)) (LMax u (LSucc v)))
  test "imax u v is not max u v" (not (isEquiv (LIMax u v) (LMax u v)))
  test "imax u 0 = 0" (isEquiv (LIMax u LZero) LZero)
  test "succ u >= u" (isGeq (LSucc u) u)
  test "u >= succ u is false" (not (isGeq u (LSucc u)))
  test "max u v >= u" (isGeq (LMax u v) u)
  test "1 + max u v = max (1+u) (1+v)" (isEquiv (LSucc (LMax u v)) (LMax (LSucc u) (LSucc v)))
  test "Prop normalizes to zero" (normalizesToZero (LIMax u LZero))
  test "succ u is not zero" (isNotZero (LSucc u) && not (isNotZero u))

  -- substitution
  let x = FVar 100
      y = FVar 101
      body = App (App (Const (nameStr "f") []) x) y
      closed = abstractFVars body [100, 101]
  test "abstract numbers outermost first" (closed == App (App (Const (nameStr "f") []) (BVar 1)) (BVar 0))
  test "instantiateRev undoes abstract" (instantiateRev closed [x, y] == body)
  test "instantiate1 replaces bvar 0" (instantiate1 (BVar 0) x == x)
  test "lowering past a binder" (instantiate1 (Lam (nameStr "z") BDefault (Sort LZero) (BVar 1)) x
                                  == Lam (nameStr "z") BDefault (Sort LZero) x)
  let lam2 = Lam (nameStr "a") BDefault (Sort LZero) (Lam (nameStr "b") BDefault (Sort LZero) (App (BVar 1) (BVar 0)))
  test "beta consumes two binders" (headBetaReduce (mkApp lam2 [x, y]) == App x y)
  test "binder names are ignored by equality" (Lam (nameStr "p") BDefault (Sort LZero) (BVar 0) == Lam (nameStr "q") BImplicit (Sort LZero) (BVar 0))
  test "let bodies are compared" (Let (nameStr "a") (Sort LZero) x (BVar 0) /= Let (nameStr "a") (Sort LZero) y (BVar 0))

  -- accepted fixtures
  forM_ ["Nat.add_succ.ndjson", "Nat.add_succ.v3.0.ndjson"] $ \f -> do
    r <- checkFile defaultCheckOptions { coSilent = True } (fixtures </> f)
    test (f ++ " is accepted") (null (rFailures r) && rFormatError r == Nothing && rChecked r > 0)

  -- an export with nothing to vouch for is never accepted
  tmp <- getTemporaryDirectory
  let emptyPath = tmp </> "tenet-hs-empty.ndjson"
      noMetaPath = tmp </> "tenet-hs-nometa.ndjson"
  B.writeFile emptyPath B.empty
  real <- B.readFile (fixtures </> "Nat.add_succ.ndjson")
  B.writeFile noMetaPath (B.drop 1 (B.dropWhile (/= 10) real))
  forM_ [("an empty file", emptyPath), ("a file without a metadata record", noMetaPath)] $ \(what, path) -> do
    r <- checkFile defaultCheckOptions { coSilent = True } path
    test (what ++ " is a format error, not OK") (rFormatError r /= Nothing)
  removeFile emptyPath
  removeFile noMetaPath

  -- the negative corpus
  manifestBytes <- B.readFile (fixtures </> "invalid" </> "manifest.json")
  cases <- case parseJson manifestBytes >>= field "cases" >>= asArray of
    Left e -> putStrLn ("cannot read manifest: " ++ e) >> exitFailure
    Right cs -> pure cs
  listed <- forM cases $ \c -> do
    let get k = either (const "") T.unpack (field k c >>= asString)
        file = get "file"
        rejects = get "rejects"
        defenseOff = case fieldMaybe "defenseOff" c of Just (JStr s) -> Just (T.unpack s); _ -> Nothing
        path = fixtures </> "invalid" </> file
    r <- checkFile defaultCheckOptions { coSilent = True } path
    test (file ++ " parses to the end") (rFormatError r == Nothing)
    let cascade = case fieldMaybe "cascade" c of
          Just (JArr xs) -> [T.unpack s' | JStr s' <- xs]
          _ -> []
    test (file ++ " rejects exactly " ++ rejects ++ concatMap (", and " ++) cascade)
      (sort (map (showName . fName) (rFailures r)) == sort (rejects : cascade))
    case defenseOff of
      Nothing -> pure ()
      Just d -> do
        test (file ++ " names a defense this checker has") (d == "TENET_NO_PRIMITIVE_CHECK")
        r2 <- checkFile defaultCheckOptions { coSilent = True, coPrimitiveCheck = False } path
        test (file ++ " is accepted in full with its defense off") (null (rFailures r2) && rFormatError r2 == Nothing)
    pure file
  onDisk <- filter ((== ".ndjson") . takeExtension) <$> listDirectory (fixtures </> "invalid")
  test "every file in invalid/ has a manifest entry, and the reverse" (sort onDisk == sort listed)

  n <- readIORef total
  f <- readIORef failures
  putStrLn (show (n - f) ++ " of " ++ show n ++ " tests passed")
  when (f > 0) exitFailure
