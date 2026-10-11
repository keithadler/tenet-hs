# tenet-hs

**An independent Lean 4 kernel in Haskell, and a checker for Lean exports.**

[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

tenet-hs re-implements the trusted core of the [Lean 4](https://lean-lang.org) theorem prover in
Haskell: expressions, universe levels, environments, type inference, definitional equality,
inductive types (mutual and nested), quotients, and native `Nat` and `String` literals. Given an
NDJSON export from [lean4export](https://github.com/leanprover/lean4export), it re-checks every
declaration from scratch and reports the first thing it cannot accept.

It is written from the type theory and the reference kernel's behavior, not translated from it,
and it shares no code with Lean or with [Tenet](https://github.com/keithadler/tenet), its sibling
on .NET. It needs nothing beyond the libraries that ship with GHC.

```
$ tenet-hs check Init.ndjson --summary
OK: 57919 checked, 0 failed, 59349 constants, 54.8s
```

## Why another kernel

This is not a flag-planting exercise. tenet-hs is a sibling of Tenet, and I will maintain the two
together, along with the rest of the family. I feel strongly that the more independent kernels
there are, the better: a proof that survives several implementations, in different languages, by
different hands, is a proof you can trust more, and every new implementation is another chance to
find a bug in the reference kernel, in the others, or in the specification they are all trying to
match.

Be precise about what independence means here. The code shares nothing with Lean or Tenet. The
algorithm is not independent: the goal is to match the reference kernel's behavior, so its
structure is followed on purpose. A flaw in the kernel's *design* is one tenet-hs would likely
reproduce rather than catch. What each additional implementation does buy is protection against
*implementation* bugs, and a cheap way to find them: two kernels that disagree on a declaration
have found something. This one already has.

## The evidence

A kernel whose check returns `True` also reports zero failures on all of `Init`, in less time. So
nothing here is evidence until it sits next to a run that *should* fail.

| | |
| --- | --- |
| **Accepts** all of `Init` (Lean 4.35.0-rc4) | 57,919 declarations, 0 failed, 55 s on one core |
| **Rejects** it when every theorem is given another theorem's proof | 41,378 rejected, **the identical 41,378 that Tenet rejects** |
| **Rejects** its [negative corpus](tests/fixtures/invalid) | 9 of 9, each at the one declaration it names, each defended case accepted in full with its defense off |
| **Agrees** with Tenet on randomly damaged files | 350 variants, 3,023 rejections, 0 disagreements |
| **Passes** the [Lean Kernel Arena](docs/arena.md)'s published suite | 196 of 196: all 71 `bad/` rejected, all 125 `good/` accepted |
| **Re-derives** every recursor | compared field for field with the exporter's, for every inductive in `Init`, nested and mutual included |

The fuzzer's first full run found **9 disagreements in 120 variants**, all one bug in how a rejected
inductive was handled. It is fixed, and the story is in [testing](docs/testing.md#the-fuzzer).
[Status](docs/status.md) has every command and every number, and what has *not* been done.

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

| Option | |
| --- | --- |
| `--fail-fast` | stop at the first rejected declaration |
| `--quiet`, `--summary` | print only the names of failures, or only the last line |
| `--only A,B` | check just these declarations and add everything else unchecked |
| `--rules` | print how often each kernel rule fired, and which never did |
| `--no-compare` | do not compare the exporter's inductive claims with what was derived |
| `--no-primitive-check` | take the `Nat`/`String` shortcuts on the name alone, as Lean's kernel does |
| `--max-unfolds N` | deterministic work bound per declaration |

Exit codes: **0** every declaration accepted, **1** something rejected, **2** the export is malformed,
**4** declined (the file needs compiled code, which an external checker will not trust).

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
  declaration is *declined*, not reported as invalid, and not trusted.
- **Reserved namespace.** `_nested` belongs to the kernel's nested-inductive elimination.
- **Recursors.** The exporter's recursors are never trusted. They are re-derived and compared.

Where it decides anything differently from Lean, [divergences](docs/divergences.md) says so.

## Other checkers

Independent checking of Lean proofs is an established practice with several existing tools.
tenet-hs is another entry, not a first.

| | What it is | Catches a bug in Lean's kernel? |
| --- | --- | --- |
| [lean4checker](https://github.com/leanprover/lean4checker) | Official. Replays a module's environment through **Lean's own kernel** | No: it shares the kernel it is checking |
| [con-leche](https://github.com/leanprover/con-leche) | An external checker written in Lean, **proven in Lean not to accept a proof of `False`** | Yes, and it is the strongest guarantee of any of these |
| [con-ron](https://github.com/leanprover/con-ron) | A Rust port of con-leche, proven equivalent to it with [Aeneas](https://aeneasverif.github.io) | A different compiler and runtime, but proven identical in behavior, so not design diversity |
| [lean4lean](https://github.com/digama0/lean4lean) | A Lean 4 kernel written in Lean 4, aimed at being verified against the type theory | Yes, and it is the most rigorous of these |
| [nanoda](https://github.com/ammkrn/nanoda_lib) | An independent kernel in Rust; the checker [Comparator](https://github.com/leanprover/comparator) drives it | Yes |
| [trepplein](https://github.com/gebner/trepplein) | An independent kernel in Scala | Yes |
| [Tenet](https://github.com/keithadler/tenet) | An independent kernel in C# on .NET | Yes |
| tenet-hs | An independent kernel in Haskell | Yes |

What tenet-hs adds is a third language, a build with no dependencies and no packages to download, and a
differential check against its sibling that has already found a real bug. What it does
not have is Tenet's reader for compiled `.olean` files or its speed: it is two to five times slower on the
arena's performance tests, and [design](docs/design.md#what-was-measured) says why, with the profiles.

## Documentation

| | |
| --- | --- |
| [Design](docs/design.md) | how it is built, and what profiling taught, including the dead ends |
| [Specification](docs/specification.md) | every typing, reduction and equality rule, next to the function that implements it |
| [Divergences](docs/divergences.md) | everywhere it differs from Lean's kernel, and from Tenet |
| [Format](docs/format.md) | the export format it reads |
| [Testing](docs/testing.md) | the seven kinds of test, and how to run each |
| [Status](docs/status.md) | what has been run, with the commands, and what has not |
| [Arena](docs/arena.md) | the Lean Kernel Arena submission |

## Limitations

- It reads lean4export NDJSON only. There is no `.olean` reader.
- It is single-threaded. `Init` takes about a minute; Mathlib would take hours, and has not been run.
- It is slower than Tenet, by two to five times on the arena's performance tests.
- Like Tenet it does not accelerate `Nat.log2`, which only makes it slower on terms that use it.
- Built and tested with one GHC version.

## License

Apache License 2.0, the same license as Lean. See [LICENSE](LICENSE).
