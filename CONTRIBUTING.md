# Contributing

tenet-hs is one of a family of independent Lean kernels, and what it is for is finding disagreements. The most
valuable contribution is an input on which this checker and another (Lean's, Tenet, lean4lean, nanoda, …)
disagree, with a note on which one is right.

## Build and test

```bash
cabal build
cabal test
```

There are no dependencies beyond the libraries that ship with GHC, and there should not be any. A checker whose
build downloads packages has a larger trusted base than one that does not.

## Before sending a change to the kernel

A green `cabal test` is not enough. Evidence for a kernel change has two halves, and both are needed:

1. **It still accepts what it should.** All of `Init` checks with 0 failures; if you can, the arena's suite is
   194/196 or better (the two it can miss are timeouts, which the arena scores as declined).
2. **It still rejects what it should.** The negative corpus passes, and the swapped-proof run rejects the same
   set as before. See [docs/testing.md](docs/testing.md). If you have Tenet built, run `tools/fuzz.py`: any
   disagreement is a bug in one of the two.

A change that makes something faster must say what it measured. The design notes record a hash-consing attempt
that looked obviously right and was ten times slower.

## Style

Match the surrounding code. Files start with the Apache header Lean uses. Comments say why, not what. American
English. No em dashes.

## Reporting a soundness bug

If tenet-hs accepts something Lean's kernel rejects, that is a soundness bug in tenet-hs and the most useful
thing you can report. See [SECURITY.md](SECURITY.md).

## License

By contributing you agree your work is released under the Apache License 2.0, as the rest of the project is.
