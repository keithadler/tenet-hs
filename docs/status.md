# Status

Version 0.1. This page says what has been run, with the command for each, and what has not. Read it as
**agreement, not soundness**: a kernel whose check returns `True` reports zero failures on all of `Init` too, in
less time. Every acceptance number here sits next to a rejection number for that reason.

## Accepted

| Input | Result | Command |
| --- | --- | --- |
| `Init`, Lean 4.35.0-rc4 (346 MB) | 57,919 declarations, **0 failed**, 48 s, 0.84 GB peak | `tenet-hs check Init.ndjson --summary` |
| **A Mathlib slice**: the import closure of `Mathlib.Algebra.Ring.Basic` (572 MB) | 128,265 declarations, **0 failed**, 68 s, 1.5 GB peak | `tenet-hs check slice.ndjson --summary` |
| **A broader Mathlib slice**: 19 areas (analysis, number theory, linear algebra, combinatorics, measure theory, algebraic geometry, category theory, Galois theory, manifolds, polynomial rings and more) with every dependency (2.55 GB) | 405,144 declarations, **0 failed**, 463 s, 4.2 GB peak | `tenet-hs check slice.ndjson --summary +RTS -xn` |
| `Init.Core`, `Init.Prelude` | 0 failed, under a second each | same |
| `Nat.add_succ`, format 3.1 and 3.0 | accepted | `cabal test` |

Every inductive in `Init`, nested and mutual ones included, had its constructors and recursors **derived by the
kernel and compared field for field** with what the exporter wrote, and all of them matched. That is the check
that the exporter's recursors, which a malicious file could get wrong, are never trusted.

## Rejected

| Input | Result | Command |
| --- | --- | --- |
| The negative corpus, 9 files | **9 of 9 rejected**, each at the one declaration its manifest entry names; each defended case accepted in full with its defense off | `cabal test` |
| `Init` with every theorem given the previous theorem's proof | **41,378 rejected**, the identical set Tenet rejects | `tools/swap-proofs.py`, then `tenet-hs check … --quiet --max-unfolds 3000000` |
| The 19-area Mathlib slice, same mutation (279,094 theorems given another's proof) | **275,042 rejected**, the identical set Tenet rejects; 130,102 still check | same |
| `Init.Core`, same mutation | 637 of 650 rejected, the identical 637 Tenet rejects | same |

The survivors of the swap are not failures. They were handed a proof of a definitionally equal statement:
`eq_comm` given a proof of the same statement, `Nat.lt_irrefl` given a proof of `¬ n + 1 ≤ n`. Tenet accepts the
same ones, which is the stronger check than inspecting them.

## Differential testing against Tenet

| | |
| --- | --- |
| `tools/fuzz.py` on `Init.Prelude`, 250 variants, 3 mutations each | 2,196 rejections, **0 disagreements** |
| `tools/fuzz.py` on `Init.Core`, 100 variants, 4 mutations each | 827 rejections, **0 disagreements** |
| `tools/fuzz.py` on `Init.Prelude` again, 150 variants, on the final memory-optimized build | 1,694 rejections, **0 disagreements** |
| The whole-`Init` swap above | the same 41,378 declarations in both |

The first full fuzzer run, before these, found **9 disagreements in 120 variants**, all one bug in failure
handling: after a rejected inductive, tenet-hs checked later declarations against the recursor it had derived,
where Tenet (correctly) uses the one the file claims. It is fixed; see
[testing](testing.md#the-fuzzer). Two independent implementations found a bug in one of them, which is the case
for having more than one.

## The Lean Kernel Arena

Against the arena's published test suite, 196 files ([how to run it](arena.md)):

| | Result |
| --- | --- |
| `bad/`, must reject (71 files) | **71 of 71 rejected** |
| `good/`, must accept (125 files) | **125 of 125 accepted** |
| the two slowest, `perf/magma-list-deep-n36` and `perf/magma-list-pair-n21` | accepted in 146 s and 25 s on this laptop, inside the arena's per-test timeouts of 390 s and 260 s |

The first run was 192 of 196. The four misses were two reader gaps (table indices that are sparse or out of order,
which the format allows) and two performance tests. The readers are fixed, and the performance tests were a memory
problem more than a speed one, see below. The arena's hardware is not this laptop, so the timing margin is
evidence and not a guarantee; a timeout there would be scored as a decline, not as a wrong answer.

## Speed and memory

| | tenet-hs | Tenet |
| --- | --- | --- |
| `Init` | 48 s, 0.84 GB peak | about 30 s on one worker |
| `perf/app-lam` | 7.4 s, 4.2 GB peak | 2.0 s |
| `perf/magma-list-deep-n21` | 6.1 s | 1.4 s |
| `perf/magma-list-pair-n21` | 25 s, 2.7 GB peak | 12 s |
| `perf/magma-list-deep-n36` | 146 s, 0.86 GB peak | 50 s |

Peak is the resident set the operating system reports, which is what the arena scores. Tenet's memory was not
re-measured here.

Two to five times slower than Tenet on the arena's `perf/` tests, and about 1.8 times slower on all of `Init`
against Tenet's own single-worker figure (Tenet's number is from its README, measured on its `.olean` path, not
re-run here; the `perf/` figures for both were measured on the same laptop). The reasons, and what did and did
not help (including an attempt at hash-consing that was ten times slower), are in
[design](design.md#what-was-measured).

## Rule coverage

`tenet-hs check … --rules` counts how often each kernel rule fires. Over all of `Init`, the arena suite and the fixtures (208 files):

| Rule | Fired | |
| --- | ---: | --- |
| `InferBVar` | 0 | a loose bound variable reaches the checker (an error) (unreachable: the loose-bound-variable guard, which refuses the term before dispatch) |
| `InferFVar` | 1,273,541 | a free variable has the type its declaration gives |
| `InferSort` | 292,305 | Sort u : Sort (u+1) |
| `InferConst` | 2,806,174 | a constant has its declared type, instantiated at the given levels |
| `InferApp` | 11,873,241 | application |
| `InferLam` | 365,989 | lambda |
| `InferPi` | 316,719 | pi, in Sort (imax u v) |
| `InferLet` | 10,977 | let |
| `InferProj` | 19,841 | structure projection |
| `InferLit` | 99,806 | Nat and String literals |
| `Beta` | 59,263,899 | (fun x => b) a reduces to b[x := a] |
| `Zeta` | 29,107 | let x := v; b reduces to b[x := v] |
| `ZetaFVar` | 4,466 | a let-bound free variable reduces to its value |
| `Delta` | 21,793,666 | unfold a definition during weak head normalization |
| `DeltaLazy` | 5,166,109 | unfold during lazy delta reduction |
| `Iota` | 9,879,432 | a recursor applied to a constructor |
| `IotaK` | 443 | K-like reduction |
| `ProjRed` | 1,398,533 | (S.mk a).i reduces to a_i |
| `QuotLift` | 243 | Quot.lift on Quot.mk |
| `QuotInd` | 2 | Quot.ind on Quot.mk |
| `NatLitOp` | 218,816 | arithmetic on Nat literals |
| `NatLitPred` | 265,651 | Nat.beq and Nat.ble on literals |
| `StringLitToCtor` | 29 | a string literal expands to a list of characters |
| `NativeReduce` | 1 | Lean.reduceBool or Lean.reduceNat (declined) |
| `DefEqSyntactic` | 11,801,655 | structurally equal |
| `DefEqSort` | 11,663 | Sort u equals Sort v after level normalization |
| `DefEqConst` | 7,174 | equal constants at equivalent levels |
| `DefEqApp` | 688,622 | congruence on applications |
| `DefEqBinding` | 133,887 | congruence under a binder |
| `DefEqEta` | 1,119 | eta for functions |
| `DefEqEtaStruct` | 1,228 | eta for structures |
| `DefEqUnitLike` | 8 | any two elements of a one-constructor type with no fields |
| `DefEqProofIrrel` | 11,371 | proof irrelevance |
| `DefEqStringLit` | 0 | a string literal against the string constructor |
| `DefEqFVar` | 0 | the same free variable (unreachable: DefEqSyntactic, which decides structurally equal terms first) |
| `DefEqReflect` | 426 | a closed term against Bool.true, reduced rather than compared |
| `DefEqLazyDeltaProj` | 10,168 | two projections of the same field, by unfolding the structures |
| `UnfoldProjApp` | 58,678 | a projection applied to arguments, unfolded during lazy delta |
| `DefEqOffset` | 11,966 | Nat literals and successor offsets compared by arithmetic |
| `DefEqLazyDelta` | 613,382 | the lazy delta loop |

One rule never fired: `DefEqStringLit`, a string literal compared against an application of the string constructor. Tenet's documentation reaches the same finding and explains it: on current Lean, `String.ofList` is a definition that lazy delta unfolds before this rule is reached, so no corpus on any version exercises it. That explanation has not been re-derived for tenet-hs, only observed (no input among 208 files reaches it). `NativeReduce` fires once, in the compiled-code fixture. `InferBVar` and `DefEqFVar` are unreachable by construction, as in the reference kernel.

## Not done yet

- **All of Mathlib.** Not checked. Two slices were (above, up to 405,144 declarations), but a complete export of
  this Mathlib (about 6.6 GB, over 100 million expression records) could not be produced: lean4export stalled at
  expression 100,663,291, which is 75% of 2^27 hash buckets, so I believe its own table resizing under memory
  pressure on this 17 GB laptop. That is the exporter's limit and not the checker's, but it means the claim is
  "slices of Mathlib", and a full run needs a machine that can export it. Projected from the slices, the checker
  would want roughly 10 GB and about 20 minutes for it. That projection is untested.
- **A `.olean` reader.** Tenet reads Lean's compiled modules directly; tenet-hs reads lean4export files only.
- **Parallelism.** Single-threaded by design for now.
- **Other GHC versions.** Built and tested with GHC 9.14.1 only. The arena's flake provides `ghc` too, and a
  different version there may need changes.
- **CI beyond one platform.** The workflow in `.github/workflows/ci.yml` passes on Linux with GHC 9.14.1 (unit tests, and the arena suite built with plain `ghc` and run under an empty environment). Nothing else has been tried.
- **Speed.** The gap to Tenet is the main open item.
- **The arena's large corpora.** Merged as [#263](https://github.com/leanprover/lean-kernel-arena/pull/263) with the corpora
  declined as a precaution; the pending bump enables all of them behind a 12 GB heap cap that turns a memory blowup into a
  decline. None of the five (`mathlib`, `cslib`, `cedar`, `con-leche`, `navier-stokes-euler`) has been run through the arena's
  harness, so there is no arena number for any of them yet.
