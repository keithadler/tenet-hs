# tenet-hs

**An independent Lean 4 kernel in Haskell, and a checker for Lean exports.**

tenet-hs re-implements the trusted core of the [Lean 4](https://lean-lang.org) theorem prover in
Haskell: expressions, universe levels, environments, type inference, definitional equality,
inductive types (mutual and nested), quotients, and native `Nat` and `String` literals. Given an
NDJSON export from [lean4export](https://github.com/leanprover/lean4export), it re-checks every
declaration from scratch and reports the first thing it cannot accept.

```
$ tenet-hs check Init.ndjson --quiet
export by lean4export, Lean 4.35.0-rc4, format 3.1.0
OK: 57919 checked, 0 failed, 59349 constants, 66.8s
```

## Why another kernel

This is not a flag-planting exercise. tenet-hs is a sibling of
[Tenet](https://github.com/keithadler/tenet) (the .NET kernel), and I will maintain the two
together, along with the rest of the family. I feel strongly that the more independent kernels
there are, the better: a proof that survives several implementations, in different languages, by
different hands, is a proof you can trust more, and every new implementation is another chance to
find a bug in the reference kernel, in the others, or in the specification they are all trying to
match.

Be precise about what independence means here. The code shares nothing with Lean or Tenet. The
algorithm is not independent: the goal is to match the reference kernel's behavior, so its
structure is followed on purpose. A flaw in the kernel's *design* is one tenet-hs would likely
reproduce rather than catch. What a second and third implementation do buy is protection against
*implementation* bugs, and a cheap way to find them: two kernels that disagree on a declaration
have found something.

## Status

Version 0.1. It follows Tenet's structure rule for rule, but rule coverage has not been measured
here yet, so a rule no test reaches would not be noticed.

A clean run is not evidence by itself, because a kernel whose check returns `True` also reports zero
failures, faster. So every acceptance number below sits next to a rejection number.

| Check | Result |
| --- | --- |
| `Init` (Lean 4.35.0-rc4), 57,919 declarations | 0 failed, 67 s, one core |
| `Init.Core` with every theorem given the previous theorem's proof | 637 of 650 rejected, the identical 637 Tenet rejects |
| The negative corpus in [`tests/fixtures/invalid`](tests/fixtures/invalid) | all 9 rejected at the one declaration the manifest names; each defended case accepted in full with its defense off |
| Recursors, constructors and inductive metadata | derived by the kernel and compared field for field with what the exporter wrote, for every inductive in `Init`, nested and mutual ones included |

See [docs/status.md](docs/status.md) for exactly what has been run.

## Using it

Built and tested with GHC 9.14.1 and cabal 3.18. There are no dependencies beyond the libraries that
ship with GHC.

```bash
cabal build exe:tenet-hs
cabal run tenet-hs -- check path/to/Export.ndjson
```

Generate an export with lean4export:

```bash
git clone https://github.com/leanprover/lean4export && cd lean4export && lake build
lake env .lake/build/bin/lean4export Init > Init.ndjson
```

Options: `--fail-fast`, `--quiet`, `--only A,B` (check just those declarations and add the rest
unchecked), `--no-compare` (skip comparing the exporter's inductive claims), `--no-primitive-check`
(take the `Nat`/`String` shortcuts on the name alone, as Lean's kernel does), `--max-unfolds N`.
The exit code is 0 when everything is accepted, 1 when something is rejected, 2 when the file is
malformed.

```bash
cabal test
```

## What it defends against

An export is somebody else's file, so the checker does not take the reference kernel's trust for
granted.

- **Primitives.** `Nat.add 2 2` reduces by adding two integers only if `Nat.add` satisfies its
  defining equations over free variables. A file that declares `Nat.add` as `fun a b => a` gets the
  ordinary, slower, correct treatment.
- **Literals.** A numeric literal means a number only if `Nat` is the two-constructor inductive
  type. Otherwise `3` would be a proof of whatever the file calls `Nat`.
- **Self-reference.** A declaration is added only after it is checked, so a theorem cannot be proved
  by itself.
- **Compiled code.** `Lean.reduceBool` and `Lean.reduceNat` need running compiled code; the
  declaration is rejected as unsupported rather than trusted.
- **Reserved namespace.** `_nested` belongs to the kernel's nested-inductive elimination.
- **Recursors.** The exporter's recursors are never trusted. They are re-derived and compared.

## Limitations

- It reads lean4export NDJSON only. There is no `.olean` reader, so it cannot check a module
  directly from a build directory the way Tenet can.
- It is single-threaded. `Init` takes about a minute; Mathlib would take hours.
- Like Tenet it does not accelerate `Nat.log2`, which only makes it slower on terms that use it.
- Failed equalities are cached on the first attempt, which can only reject more; a rejected
  declaration is re-checked with the reference algorithm before it is reported.
- It has not been run against Mathlib.

## Layout

| Module | |
| --- | --- |
| `Tenet.Name`, `Tenet.Level`, `Tenet.Expr`, `Tenet.ExprOps` | names, universe levels and their normalization, expressions with cached metadata, substitution |
| `Tenet.Env` | constants, declarations, the environment |
| `Tenet.TypeChecker` | inference, weak head normalization, definitional equality, primitives |
| `Tenet.Quot`, `Tenet.Inductive` | quotients; inductive types, recursor derivation, nested elimination |
| `Tenet.Add` | checking a declaration and adding it, with rollback |
| `Tenet.Json`, `Tenet.Export`, `Tenet.Check` | the export reader and the replay driver |

## License

Apache License 2.0, the same license as Lean. See [LICENSE](LICENSE).
