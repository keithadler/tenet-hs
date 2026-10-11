{-
Copyright (c) 2026 Keith Adler and the tenet-hs contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keith Adler
-}
-- | The kernel's rules, named one by one, and how often each fired.
--
-- "All of Init checks with no failures" says nothing about which rules were exercised: a rule no input ever
-- reaches is untested however many declarations passed through it, and a green run cannot tell a rule that works
-- from one that is never called. Counting turns that from an assumption into a measurement. Run the inputs, print
-- the table, and any rule sitting at zero is a hole in the evidence.
--
-- Counting is off unless 'enableRules' is called; the cost when off is one read of a flag.
module Tenet.Rules (Rule (..), enableRules, fire, ruleCounts, subsumedBy, ruleDescription) where

import Control.Monad (when)
import Data.Array.Base (unsafeRead, unsafeWrite)
import Data.Array.IO (IOUArray, newArray)
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)

data Rule
  -- typing
  = InferBVar | InferFVar | InferSort | InferConst | InferApp | InferLam | InferPi | InferLet | InferProj | InferLit
  -- reduction
  | Beta | Zeta | ZetaFVar | Delta | DeltaLazy | Iota | IotaK | ProjRed | QuotLift | QuotInd
  | NatLitOp | NatLitPred | StringLitToCtor | NativeReduce
  -- definitional equality
  | DefEqSyntactic | DefEqSort | DefEqConst | DefEqApp | DefEqBinding | DefEqEta | DefEqEtaStruct | DefEqUnitLike
  | DefEqProofIrrel | DefEqStringLit | DefEqFVar | DefEqReflect | DefEqLazyDeltaProj | UnfoldProjApp
  | DefEqOffset | DefEqLazyDelta
  deriving (Eq, Show, Enum, Bounded)

{-# NOINLINE enabledRef #-}
enabledRef :: IORef Bool
enabledRef = unsafePerformIO (newIORef False)

{-# NOINLINE countsRef #-}
countsRef :: IOUArray Int Int
countsRef = unsafePerformIO (newArray (0, fromEnum (maxBound :: Rule)) 0)

enableRules :: IO ()
enableRules = writeIORef enabledRef True

-- | Record that a rule fired.
fire :: Rule -> IO ()
fire r = do
  on <- readIORef enabledRef
  when on $ do
    let i = fromEnum r
    n <- unsafeRead countsRef i
    unsafeWrite countsRef i (n + 1)
{-# INLINE fire #-}

ruleCounts :: IO [(Rule, Int)]
ruleCounts = mapM (\r -> (,) r <$> unsafeRead countsRef (fromEnum r)) [minBound .. maxBound]

-- | Rules no input can reach, because an earlier check decides the same case first. They are kept because the
-- reference kernel has the branch in the same place, and a coverage table that lumped them in with untested rules
-- would report work still to do where there is none.
subsumedBy :: Rule -> Maybe String
subsumedBy DefEqFVar = Just "DefEqSyntactic, which decides structurally equal terms first"
subsumedBy InferBVar = Just "the loose-bound-variable guard, which refuses the term before dispatch"
subsumedBy _ = Nothing

ruleDescription :: Rule -> String
ruleDescription = \case
  InferBVar -> "a loose bound variable reaches the checker (an error)"
  InferFVar -> "a free variable has the type its declaration gives"
  InferSort -> "Sort u : Sort (u+1)"
  InferConst -> "a constant has its declared type, instantiated at the given levels"
  InferApp -> "application"
  InferLam -> "lambda"
  InferPi -> "pi, in Sort (imax u v)"
  InferLet -> "let"
  InferProj -> "structure projection"
  InferLit -> "Nat and String literals"
  Beta -> "(fun x => b) a reduces to b[x := a]"
  Zeta -> "let x := v; b reduces to b[x := v]"
  ZetaFVar -> "a let-bound free variable reduces to its value"
  Delta -> "unfold a definition during weak head normalization"
  DeltaLazy -> "unfold during lazy delta reduction"
  Iota -> "a recursor applied to a constructor"
  IotaK -> "K-like reduction"
  ProjRed -> "(S.mk a).i reduces to a_i"
  QuotLift -> "Quot.lift on Quot.mk"
  QuotInd -> "Quot.ind on Quot.mk"
  NatLitOp -> "arithmetic on Nat literals"
  NatLitPred -> "Nat.beq and Nat.ble on literals"
  StringLitToCtor -> "a string literal expands to a list of characters"
  NativeReduce -> "Lean.reduceBool or Lean.reduceNat (declined)"
  DefEqSyntactic -> "structurally equal"
  DefEqSort -> "Sort u equals Sort v after level normalization"
  DefEqConst -> "equal constants at equivalent levels"
  DefEqApp -> "congruence on applications"
  DefEqBinding -> "congruence under a binder"
  DefEqEta -> "eta for functions"
  DefEqEtaStruct -> "eta for structures"
  DefEqUnitLike -> "any two elements of a one-constructor type with no fields"
  DefEqProofIrrel -> "proof irrelevance"
  DefEqStringLit -> "a string literal against the string constructor"
  DefEqFVar -> "the same free variable"
  DefEqReflect -> "a closed term against Bool.true, reduced rather than compared"
  DefEqLazyDeltaProj -> "two projections of the same field, by unfolding the structures"
  UnfoldProjApp -> "a projection applied to arguments, unfolded during lazy delta"
  DefEqOffset -> "Nat literals and successor offsets compared by arithmetic"
  DefEqLazyDelta -> "the lazy delta loop"
