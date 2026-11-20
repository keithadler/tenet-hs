# Changelog

## 0.1.4

Lean 4.36.0 and 4.37.0-rc1. Lean 4.36.0 changed nothing in its kernel's decisions; 4.37.0-rc1 changed three
definitional-equality rules, and tenet-hs now follows the Lean version an export names:

- Proof irrelevance is tried before the first weak head normalization of a comparison, not after (lean4#15103).
- A recursor's major premise is not reduced when it is a proof. It is eta-expanded when its structure's recursor
  eliminates into every sort, which now includes `And` and other subsingleton structures in `Prop` (lean4#15371).
- Structure eta applies against a partially applied constructor (lean4#15373).

For an export from Lean 4.37 or later (a 4.37 nightly from 2026-10-21 on) the new rules apply; for anything earlier,
or a missing or unparsable version, the old ones do, unchanged. Two new fixtures pin both directions:
`eta437.ndjson` (accepted as 4.37, exactly `Eta437.andMajor` and `Eta437.partialCtor` rejected as 4.36) and
`acc436.ndjson` (accepted as 4.36, exactly `Acc436.accReduces` rejected as 4.37). Lean's own kernels of those two
versions give the same verdicts on the same files. The negative corpus gains `partial-constructor-eta.ndjson` (an
arbitrary function is not a partial constructor) and `loose-bvar-inductive.ndjson`.

Also, for every Lean version: a loose bound variable in an inductive type or constructor type is refused up front, as
Lean 4.37 does (lean4#16512; the file was already rejected, later and with a less direct message), and an integer in
the export that does not fit a 64-bit `Int` is a format error rather than being wrapped. Lean 4.37 fixed the same
class at 32 bits (lean4#16279); tenet-hs never truncated at 32 bits, but before this change a projection index or a
parameter count of 2^64 was read as 0. Checked on `eta437.ndjson` with its two field-0 projection indices rewritten
to 2^64: 0.1.3 accepts `And.left`, Lean 4.37.0-rc1's kernel rejects it ("invalid projection"), and tenet-hs now
refuses the file as malformed. Found by reading the reader, not by a file in the wild; lean4export never writes such
an index.

Native reduction is declined or rejected according to the Lean that wrote the export. Lean 4.35 removed in-kernel native
reduction (`reduce_native` is gone from its `type_checker.cpp` from 4.35.0-rc1; `Lean.ofReduceBool` no longer exists, and
`native_decide` already produced a per-proof axiom on 4.34). For an export from Lean 4.35 or later, `Lean.reduceBool` and
`Lean.reduceNat` are now ordinary constants, so a file that leans on them is rejected as a type mismatch (exit 1), as in Lean.
For 4.34 and earlier, and for an export whose Lean version is missing, unparsable or a nightly, tenet-hs still declines
(exit 4). Real 4.35 exports do not contain these terms, so no verdict on a real library changes. The spec has 26 new
checks; ignoring the new flag makes three of them fail.

## 0.1.3

No code change. Checked against Lean 4.35.0: `Init` exported from it has 57,919 declarations, 0 failed, the same count
Tenet and the reference kernel report. Lean 4.35.0 removed native reduction from its kernel, so `Lean.reduceBool` and
`Lean.reduceNat` no longer reduce in the reference either. tenet-hs still declines them (exit 4) where 4.35.0 reports
an ordinary type mismatch; tenet-jvm already rejects them.

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
