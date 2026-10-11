{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
module Main (main) where

import Control.Monad (forM_, unless, when)
import Data.List (intercalate)
import System.Environment (getArgs)
import System.Exit
import System.IO
import Tenet.Check
import Tenet.Env (Primitive)
import Tenet.Export (ExportMeta (..))

usage :: String
usage = unlines
  [ "tenet-hs " ++ version ++ ": an independent Lean 4 kernel in Haskell"
  , ""
  , "usage: tenet-hs check FILE.ndjson [options]"
  , ""
  , "options:"
  , "  --fail-fast            stop at the first rejected declaration"
  , "  --quiet                print only the name of each failure, not the reason"
  , "  --only A,B             check just these declarations; add everything else unchecked"
  , "  --no-compare           do not compare the exporter's inductive/recursor claims with the kernel's"
  , "  --no-primitive-check   take the Nat/String shortcuts on the name alone, as Lean's kernel does"
  , "  --max-unfolds N        deterministic work bound per declaration (default 100000000)"
  , "  --version, --help"
  ]

version :: String
version = "0.1.0"

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> hPutStr stderr usage >> exitWith (ExitFailure 2)
    ["--help"] -> putStr usage
    ["-h"] -> putStr usage
    ["--version"] -> putStrLn version
    ("check" : rest) -> runCheck rest
    _ -> hPutStr stderr usage >> exitWith (ExitFailure 2)

splitCommas :: String -> [String]
splitCommas s = case break (== ',') s of
  (a, []) -> [a]
  (a, _ : r) -> a : splitCommas r

runCheck :: [String] -> IO ()
runCheck argv = do
  (file, opts) <- parse argv Nothing defaultCheckOptions
  path <- maybe (hPutStrLn stderr "tenet-hs: no input file" >> exitWith (ExitFailure 2)) pure file
  hSetBuffering stdout LineBuffering
  r <- checkFile opts path
  forM_ (rMeta r) $ \m ->
    unless (coQuiet opts) $ putStrLn ("export by " ++ mExporter m ++ ", Lean " ++ mLean m ++ ", format " ++ mFormat m)
  forM_ (rFormatError r) $ \e -> hPutStrLn stderr ("tenet-hs: malformed export, " ++ e)
  unless (null (rUnvalidated r)) $
    putStrLn ("note: these primitives did not match their defining equations and were unfolded instead of shortcut: "
              ++ intercalate ", " (map show (rUnvalidated r :: [Primitive])))
  let nfail = length (rFailures r)
      secs = show (fromIntegral (round (rSeconds r * 10) :: Int) / 10 :: Double)
  if nfail == 0 && rFormatError r == Nothing
    then putStrLn ("OK: " ++ show (rChecked r) ++ " checked, 0 failed, " ++ show (rConstants r) ++ " constants, " ++ secs ++ "s")
    else do
      putStrLn ("FAILED: " ++ show (rChecked r) ++ " checked, " ++ show nfail ++ " failed, " ++ secs ++ "s")
      when (rFormatError r /= Nothing) $ exitWith (ExitFailure 2)
      exitWith (ExitFailure 1)
  where
    parse [] file opts = pure (file, opts)
    parse ("--fail-fast" : r) f o = parse r f o { coFailFast = True }
    parse ("--quiet" : r) f o = parse r f o { coQuiet = True }
    parse ("--no-compare" : r) f o = parse r f o { coCompareInductive = False }
    parse ("--no-primitive-check" : r) f o = parse r f o { coPrimitiveCheck = False }
    parse ("--only" : v : r) f o = parse r f o { coOnly = Just (splitCommas v) }
    parse ("--max-unfolds" : v : r) f o = parse r f o { coMaxUnfolds = read v }
    parse (a@('-' : _) : _) _ _ = hPutStrLn stderr ("tenet-hs: unknown option " ++ a) >> exitWith (ExitFailure 2)
    parse (a : r) Nothing o = parse r (Just a) o
    parse (a : _) (Just _) _ = hPutStrLn stderr ("tenet-hs: unexpected argument " ++ a) >> exitWith (ExitFailure 2)
