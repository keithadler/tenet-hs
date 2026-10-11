# The Lean Kernel Arena

<https://arena.lean-lang.org> benchmarks Lean proof checkers against a shared test suite and scores them on
completeness, soundness, time (instructions retired) and memory. [`packaging/arena/tenet-hs.yaml`](../packaging/arena/tenet-hs.yaml)
is the checker definition to contribute to <https://github.com/leanprover/lean-kernel-arena> under `checkers/`.
It is kept here so it is version controlled alongside the thing it describes, and so the exit-code mapping is
reviewed whenever the command line's exit codes change. The submission process follows
[Tenet's](https://github.com/keithadler/tenet/tree/main/packaging/arena), which went through it first.

## How a checker is run

| | |
| --- | --- |
| build | `build:` in the definition, run once, in the arena's own Nix shell |
| run | `run:` once per test, with `$IN` pointing at an NDJSON export |
| exit 0 | proof accepted |
| exit 1 | proof rejected |
| exit 2 | **declined**: the checker will not vouch for it. Scored as neither right nor wrong |
| anything else | an error in the checker, which is a bug |
| timeout | per test, set by the test; scored like a decline |

## Why this build needs nothing

The arena's flake already provides `ghc`, and tenet-hs depends only on the libraries that ship with it. So the
build line is a single `ghc --make`, with no cabal and no package downloads, and nothing had to be added to the
arena's flake. The flags in the definition are the extensions the cabal file turns on for every module; if one is
added there, it has to be added there too (CI builds both ways, so a mismatch fails).

## Declining, which is a matter of honesty

`Lean.reduceBool` and `Lean.reduceNat` make a kernel run compiled code. tenet-hs refuses, because a checker that
ran the output of a compiler and a runtime would be trusting exactly what an independent checker exists not to
trust. It used to report this as a failed declaration, which reads as a claim the proof is invalid. It is not a
claim that; it is a claim that this checker will not vouch for it.

So `tenet-hs check` exits **4** and prints `DECLINED` when every failure is of that kind, and the run line maps 4
to the arena's 2. Exit 2 is already taken by "malformed export", which is why the numbers differ. The negative
corpus records which outcome each case expects, so the distinction cannot quietly collapse in either direction.

## One worker

The definition declares no `threads`, so the arena reserves its default of one CPU slot. That is the honest
number: declarations are checked in order in one thread. Declaring more than the checker uses would idle the
runner; declaring fewer than it uses would steal CPU from whatever runs alongside. See
[design](design.md#why-single-threaded).

## Running the suite locally

```bash
curl -O https://arena.lean-lang.org/lean-arena-tests.tar.gz
mkdir suite && tar -xzf lean-arena-tests.tar.gz -C suite
tools/arena.sh suite
```

`tools/arena.sh` applies the same exit-code mapping as the definition, with a per-file time limit
(`ARENA_TIMEOUT`, default 300 s). Current results are in [status](status.md#the-lean-kernel-arena).

## Submitting

1. Push this repository and note the commit.
2. Replace `REPLACE_WITH_REV` in the definition with that commit.
3. Validate it against the arena's `schemas/checker.json`.
4. Open a pull request adding the file as `checkers/tenet-hs.yaml`.

The arena does not update checkers automatically; a new release is a new pull request.
