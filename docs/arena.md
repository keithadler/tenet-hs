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

## Every corpus is enabled, and memory has a cap

The definition does not decline any test. The arena's large corpora are `init` (332 MB), `std` (569 MB), `con-leche`
(526 MB), `cedar` (832 MB), `navier-stokes-euler` (1.5 GB), `cslib` (2.3 GB) and `mathlib` (5.8 GB, 110 million
lines). tenet-hs has checked all of `Init`, and slices of Mathlib up to a 2.55 GB export with 405,144 declarations,
so every corpus but `mathlib` is no larger than something already checked. `mathlib` is 2.3 times larger than the
largest slice, and projected from it would want about 10 GB and about twenty minutes against a timeout of 5,680 s.
That projection is untested, because a complete Mathlib export could not be produced on the development machine.

An earlier version of the definition declined these five corpora as a precaution. That was too conservative: the
arena scores a timeout as a decline anyway, so declining only forfeited any chance of a result.

The risk worth guarding is memory. The run line gives the runtime a 12 GB heap cap, and the runtime exits with
code 251 when it is reached. The run line maps 251 to the arena's decline, exactly as it maps the compiled-code
decline (4), so a corpus that needs more memory than the cap is scored as declined and not as an error. The same
line selects the non-moving collector (`+RTS -xn`), which costs about 6% in time and saves about a third of peak
memory on inputs of this size. Both were checked from a fresh clone: a corpus run under a deliberately tiny cap
exits 2, and the whole published suite gives the same verdicts with the flags as without.

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

tenet-hs was added in [#263](https://github.com/leanprover/lean-kernel-arena/pull/263). To submit a new release:

1. Push the release and note the commit.
2. Set `rev` and `version` in the definition, and validate it against the arena's `schemas/checker.json`.
3. Check it from a fresh clone: run the `build` and `run` lines under `env -i` on a file that should be accepted, one that
   should be rejected, one that is declined, and one run under a deliberately tiny heap cap.
4. Open a pull request changing `checkers/tenet-hs.yaml`.

The arena does not update checkers automatically; a new release is a new pull request. Text written by Claude is
marked as such in the pull request, as the arena's maintainers asked.
