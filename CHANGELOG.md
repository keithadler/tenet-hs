# Changelog

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

Measured: all of `Init` (Lean 4.35.0-rc4), 57,919 declarations, 0 failed. Every theorem in `Init` given the
previous theorem's proof: the same 41,378 rejected by this checker and by Tenet. The Lean Kernel Arena's
published suite: see [docs/status.md](docs/status.md).
