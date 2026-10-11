# Test fixtures

Copied from [Tenet](https://github.com/keithadler/tenet) (MIT OR Apache-2.0), so both kernels are measured
against the same files.

- `Nat.add_succ.ndjson`: `Nat.add_succ` with its transitive dependencies, produced by lean4export
  (format 3.1.0, Lean 4.34.0-rc2).
- `Nat.add_succ.v3.0.ndjson`: the example shipped with lean4export (format 3.0.0, Lean 4.27.0-rc1). It spells
  the inductive block's fields `inductiveVals`, `constructorVals` and `recursorVals`; the reader accepts both.
- `invalid/`: exports that must be rejected, one declaration each, named in `manifest.json`. With the defense
  a case targets switched off the file must be accepted in full; that second assertion is what stops a case
  passing because the file is broken rather than because the defense works.

The exported content is derived from the Lean 4 standard library and lean4export, both Apache License 2.0,
Copyright Lean FRO and contributors.

Larger exports (`Init.Prelude`, `Init.Core`, all of `Init`) are generated, never committed; see the README.
