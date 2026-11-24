# Test fixtures

Copied from [Tenet](https://github.com/keithadler/tenet) (MIT OR Apache-2.0), so both kernels are measured
against the same files.

- `Nat.add_succ.ndjson`: `Nat.add_succ` with its transitive dependencies, produced by lean4export
  (format 3.1.0, Lean 4.34.0-rc2).
- `Nat.add_succ.v3.0.ndjson`: the example shipped with lean4export (format 3.0.0, Lean 4.27.0-rc1). It spells
  the inductive block's fields `inductiveVals`, `constructorVals` and `recursorVals`; the reader accepts both.
- `eta437.ndjson`: three declarations Lean 4.37 accepts and 4.36 rejects, with their dependencies, exported by Lean
  4.37.0-rc1 from `sources/Eta437.lean`: eta for the major premise of `And.rec` (lean4#15371) and eta against a
  partially applied structure constructor (lean4#15373). With the metadata rewritten to an earlier Lean, exactly
  `Eta437.andMajor` and `Eta437.partialCtor` must fail, which is what Lean 4.36.0's kernel says of the same file.
- `acc436.ndjson`: the other direction, exported by Lean 4.36.0 from `sources/Acc436.lean`: `Acc.rec` applied to a
  proof that has to be unfolded to reach `Acc.intro`. Lean 4.37 does not reduce a proof standing as a major premise,
  so with the metadata rewritten to 4.37 exactly `Acc436.accReduces` must fail, as in Lean 4.37.0-rc1's kernel.
- `sources/`: the Lean files those two were exported from, and `stitch.py`, which adds the must-reject `boxEta` to
  the first to make `invalid/partial-constructor-eta.ndjson`.
- `invalid/`: exports that must be rejected, one declaration each, named in `manifest.json`. With the defense
  a case targets switched off the file must be accepted in full; that second assertion is what stops a case
  passing because the file is broken rather than because the defense works.

The exported content is derived from the Lean 4 standard library and lean4export, both Apache License 2.0,
Copyright Lean FRO and contributors.

Larger exports (`Init.Prelude`, `Init.Core`, all of `Init`) are generated, never committed; see the README.
