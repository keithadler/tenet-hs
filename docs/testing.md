# Testing

A checker that accepts everything also reports zero failures, faster. So nothing in this project is evidence
until it sits next to a run that *should* fail, and the pages below keep the two together. Seven kinds of test,
from fastest to slowest.

## 1. Unit tests and the negative corpus

```bash
cabal test
```

[`tests/Spec.hs`](../tests/Spec.hs) covers universe levels (normalization, `imax`, the order), substitution
(abstract, instantiate, beta, the binder-name rule of equality), the two committed fixtures, and the negative
corpus. About a second.

### The negative corpus

[`tests/fixtures/invalid`](../tests/fixtures/invalid) holds well-formed exports that **must be rejected**, one
declaration each, named in `manifest.json`: `Type : Type`, a non-positive inductive, a `Prop` that eliminates
into `Sort u`, a theorem proved by itself, a swapped proof, a squatted reserved namespace, a claim laundered
through compiled code, a `Nat` that is not a `Nat`, and a `Nat.add` that is not addition. The runner checks
three things for each:

- the file parses to the end;
- exactly the declaration the manifest names is rejected, and nothing else, so a case cannot pass by being broken
  somewhere unrelated;
- where a case targets an optional defense, the file is **accepted in full** with that defense switched off.
  Without this a case could keep passing after the defense was deleted.

Adding a file without a manifest entry fails, and so does an entry that names a file that is missing.

## 2. Real libraries

Exports are large and never committed; generate them with lean4export:

```bash
git clone https://github.com/leanprover/lean4export && cd lean4export && lake build
mkdir -p ~/tenet-hs-exports
for m in Init.Prelude Init.Core Init; do
  lake env .lake/build/bin/lean4export $m > ~/tenet-hs-exports/$m.ndjson
done
```

```bash
cabal run -v0 tenet-hs -- check ~/tenet-hs-exports/Init.ndjson --summary
```

All of `Init` is 346 MB, 57,919 declarations, about a minute. It needs 2.3 GB of memory, because every
expression of the export stays alive (later declarations refer to earlier ones by index, and the environment
needs every type and value for unfolding).

## 3. Mutation: swap the proofs

```bash
python3 tools/swap-proofs.py ~/tenet-hs-exports/Init.ndjson ~/tenet-hs-exports/Init.swapped.ndjson
cabal run -v0 tenet-hs -- check ~/tenet-hs-exports/Init.swapped.ndjson --quiet --max-unfolds 3000000
```

Every theorem gets the previous theorem's proof. Nearly all of them become wrong and a kernel has to say so; the
ones still accepted had a proof of a definitionally equal statement (`eq_comm` given a proof of the same
statement, `¬ n < n` given `¬ n+1 ≤ n`). A bound on unfoldings keeps the few exponential failures from running
for minutes; a timeout is still a rejection, which is the right verdict for a mutated proof.

## 4. Differential testing against Tenet

The same file through two independent implementations. A disagreement on any declaration is a bug in one of
them, and has been (see below).

```bash
export DOTNET_ROOT=$HOME/.dotnet
tenet check Init.swapped.ndjson > tenet.out
tenet-hs check Init.swapped.ndjson --quiet > hs.out
diff <(grep -o '^FAIL [a-z]* [^ ]*' tenet.out | sort) <(grep -o '^FAIL [a-z]* [^ ]*' hs.out | sort)
```

### The fuzzer

```bash
python3 tools/fuzz.py ~/tenet-hs-exports/Init.Prelude.ndjson --seeds 250 --mutations 3
```

[`tools/fuzz.py`](../tools/fuzz.py) damages an export at random points and compares the two kernels' sets of
rejected declarations. Each variant redirects a few references in the expression table (an application's
function or argument, a binder's type or body, a projection's index or structure, a bound variable's index, a
literal's value) to another entry, so the file stays well formed and only its meaning changes. Both checkers
must reject exactly the same declarations.

**It found a real divergence on its first full run.** Nine of 120 variants disagreed, always in the same
shape: Tenet rejected `X.casesOn` and `X.recOn` downstream of a mutated inductive and tenet-hs accepted them.
The cause was failure handling, not the type theory. When the exporter's recursor disagreed with the derived
one, tenet-hs kept its own correct recursor and judged later declarations against *that*; Tenet installs what
the file actually says, which is the right behavior (downstream code is judged against the file's claims, not
against what the file should have claimed). Fixed, and all nine agree.

## 5. The Lean Kernel Arena's suite

```bash
curl -O https://arena.lean-lang.org/lean-arena-tests.tar.gz
mkdir suite && tar -xzf lean-arena-tests.tar.gz -C suite
tools/arena.sh suite
```

[`tools/arena.sh`](../tools/arena.sh) runs every file in `good/` (must accept) and `bad/` (must reject) and maps
exit codes the way the arena does. See [arena.md](arena.md).

## 6. Rule coverage

```bash
tenet-hs check Init.ndjson --summary --rules
```

Prints how often each kernel rule fired. A rule at zero is a part of the kernel no input has exercised, however
many declarations passed through. `DefEqFVar` is listed as unreachable because an earlier check always decides
the same case, as it is in the reference kernel.

## 7. Reading a failure

```
FAIL thm Nat.add_succ (0.01s)
    declaration type mismatch for 'Nat.add_succ'
      expected: …
      inferred: …
```

Every failure names the declaration, the kernel's reason, and how long it took. By default the checker keeps
going after a failure, installing the exporter's own view of the failed declaration so later ones can still be
checked; `--fail-fast` stops at the first. `--only A,B` checks just those declarations and adds everything else
unchecked, which is the quick way to iterate on one. `--quiet` prints only names, `--summary` only the last line.

## Exit codes

| code | meaning |
| --- | --- |
| 0 | every declaration accepted |
| 1 | something was rejected |
| 2 | the export is malformed |
| 4 | declined: the file needs compiled code (`Lean.reduceBool`), which an external checker will not trust |
