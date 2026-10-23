# Changelog

## 0.1.2

A robustness fix.

- A declaration whose reduction nests deeply enough to exhaust the stack is now reported as undecided
  (`unsupported: expression too deep…`, exit 4 if nothing else failed) and the run carries on. Before, GHC's
  `StackOverflow` was uncaught and ended the whole run with exit 2, which reads as a malformed export. Found by giving
  every theorem in a Mathlib-sized export another theorem's proof: `ISize.toInt_ofNat_of_lt._proof_1_2` sent
  reduction away. Tenet reports the same declaration as a failure, "expression too deep".

The Lean Kernel Arena has run tenet-hs on all 233 of its tests: 207 correct and 26 "either", with no wrong answer,
decline, error or timeout, including the whole of `mathlib` (accepted in 2746 s, 12.3 GB peak), `cslib`, `cedar`,
`con-leche` and `navier-stokes-euler`. It is among the slowest kernels that accept `mathlib`. See
[docs/status.md](docs/status.md).

## 0.1.1

Memory, and a Mathlib result.

- About 2.5 times less memory. Expression metadata is two words instead of five plus an indirection, the import
  tables are mutable arrays instead of maps, entries and constant fields are strict, and the input is streamed
  with a strict counter. `Init` peaks at 0.84 GB (was 2.5 GB); the arena's heaviest test, `magma-list-deep-n36`,
  at 0.86 GB and 146 s (was 1.5 GB and 199 s); `magma-list-pair-n21` at 2.7 GB and 25 s (was 5.0 GB and 34 s).
- Two slices of Mathlib check: 128,265 and 405,144 declarations, 0 failed. With every proof swapped, the larger
  slice rejects the identical 275,042 declarations Tenet does. All of Mathlib has not been checked: lean4export
  stalled while exporting it.
- The Lean Kernel Arena's published suite is still 196 of 196, and 150 more fuzzed variants agree with Tenet.

## 0.1.0

First release. A Lean 4 kernel in Haskell and a checker for lean4export files.

- Expressions, universe levels (with normalization and the kernel's equality), environments, type inference,
  weak head normalization, and definitional equality with lazy delta reduction, proof irrelevance, eta for
  functions and structures, K-like reduction, quotients, and native `Nat` and `String` literals.
- Inductive types, mutual and nested: positivity, universes, the elimination universe, and the recursors and
  their computation rules, derived by the kernel and compared field for field with the exporter's.
- Accelerated primitives are validated against their defining equations before they are trusted; a literal's
  type is checked against the environment; `_nested` is reserved; `Lean.reduceBool` and `Lean.reduceNat` are
  declined (exit 4) and not reported as invalid.
- Reads format 3.0 and 3.1, with sparse and out-of-order table indices.
- `--rules` reports which kernel rules an input exercised.

Measured: all of `Init` (Lean 4.35.0-rc4), 57,919 declarations, 0 failed, 48 s, 0.84 GB. A 19-area Mathlib slice,
405,144 declarations, 0 failed, with the identical 275,042 swapped proofs rejected as by Tenet. Every theorem in `Init` given the
previous theorem's proof: the same 41,378 rejected by this checker and by Tenet. 350 randomly damaged files:
3,023 rejections, 0 disagreements with Tenet. The Lean Kernel Arena's published suite: 196 of 196. See
[docs/status.md](docs/status.md) for every command, and for what has not been done.
