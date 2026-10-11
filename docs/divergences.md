# Divergences

tenet-hs aims to decide exactly what Lean's kernel decides. Anywhere it does not, and the difference is not
listed here, it is a bug and should be reported. The practice, and the name of this file, is borrowed from
[lean4lean](https://github.com/digama0/lean4lean/blob/master/divergences.md) and from
[Tenet](https://github.com/keithadler/tenet/blob/main/docs/divergences.md), whose list this one starts from.

Two lists follow: where tenet-hs decides differently from **Lean**, and where it differs from **Tenet**, its
sibling. They are different questions. Disagreeing with Tenet on an input is how a bug in either gets found, so
the second list is short on purpose and every entry in it is a gap, not a choice.

## Against Lean's kernel

| | Divergence | Kind |
| --- | --- | --- |
| 1 | An accelerated primitive is checked before it is trusted | **Threat model** |
| 2 | A literal's type is checked against the environment | **Threat model** |
| 3 | The `_nested` namespace is reserved | **Threat model** |
| 4 | `Lean.reduceBool` and `Lean.reduceNat` are declined | **Threat model** |
| 5 | Failure caching, then a faithful re-check | **Optimization, observationally neutral** |
| 6 | A bound on work | **Resource** |
| 7 | The string constructor is read from the environment | **Compatibility** |
| 8 | No acceleration for `Nat.log2` | **Missing optimization, never a wrong answer** |

**Threat model (1 to 4).** Not disagreements about what is true. Lean ships its own prelude and does not support
replacing it, so deciding from the name that `Nat.add` is addition, or that a numeral is a `Nat`, is sound *for
Lean*. tenet-hs reads a file somebody else produced, which is its entire purpose, so the same shortcuts are
holes. In each case it ends up closer to the type theory than Lean is, by doing work Lean can correctly skip.
None of these can arise on an honest export.

### An accelerated primitive is checked before it is trusted

**Where:** `checkPrimitive`, consulted by `reduceNat`, in `Tenet.TypeChecker`.

**What Lean does:** computes `Nat.add 2 2` by adding two machine integers rather than unfolding the declaration,
and decides to from the name alone. Nothing checks that the constant called `Nat.add` is addition.

**What tenet-hs does:** takes the shortcut only for a constant whose behavior it has checked. `Nat.succ` is
checked to be the constructor with the right type. `pred`, `add`, `sub`, `mul`, `pow`, `beq` and `ble` are
checked against their defining equations over free variables (`add x 0 ≡ x`, `add x (succ y) ≡ succ (add x y)`, and so on). `div`, `mod`, `gcd`, the bitwise
operations and the shifts are recursions with no clause form, so they are exercised at sampled values instead,
which detects a substituted implementation and does not prove agreement everywhere. A constant that fails is
unfolded rather than rejected, so an unusual but honest prelude is checked slowly instead of refused.

**Evidence it matters:** `tests/fixtures/invalid/primitive-body.ndjson` declares `Nat.add` as `fun a b => a`.
With the check the file is rejected at the one declaration that relies on `Nat.add 2 2` being 4; with
`--no-primitive-check` it is accepted in full, which is what shows the rejection is the defense and not a broken
file.

### A literal's type is checked against the environment

**Where:** `inferLit`, `checkPrimitive` for `PNatLiteralType` and `PStringLiteralType`.

**What Lean does:** a numeric literal has type `Nat`, asserted by its representation.

**What tenet-hs does:** also requires `Nat` to be the two-constructor inductive the literal means. Otherwise a
file that declares its own `Nat` as a proposition makes `3` a proof of it, and if that proposition is `False` the
file has proved `False` with no axioms. `tests/fixtures/invalid/literal-type.ndjson` is exactly that file.

### The `_nested` namespace is reserved

**Where:** `addCoreDecl` in `Tenet.Add`.

Nested-inductive elimination generates auxiliary types into `_nested.*`. Lean reserves the namespace against
ordinary declarations; tenet-hs checks for it explicitly, since a file can otherwise squat on a name the kernel
is about to derive. The kernel's own auxiliaries are installed with `addCore`, so this costs a legitimate file
nothing.

### `Lean.reduceBool` and `Lean.reduceNat` are declined

**Where:** `reduceNative`; the exit code is in `app/Main.hs`.

**What Lean does:** runs compiled code to evaluate the argument.

**What tenet-hs does:** refuses. A checker that ran the output of compiled code would be trusting a compiler and
a runtime, which is the thing an independent checker exists to avoid. The declaration is reported as
**declined**, and the process exits **4**, not as rejected. A decline is not a claim the proof is invalid; it is a
claim that this checker will not vouch for it. The Lean Kernel Arena has the same distinction (its exit code 2).

### Failure caching, then a faithful re-check

Caching *failed* definitional-equality results can only make the checker stricter, since definitional equality is
not transitive. So the first attempt at a declaration caches failures, and a declaration rejected that way is
re-checked with the cache off. The verdict reported is the reference algorithm's. Nothing is observable except
speed.

### A bound on work

`--max-unfolds N` (default 100,000,000) bounds the definition unfoldings per checker. The theory has no notion
of running out of work; an external checker needs one, because `unsafe def f : Nat := f` would otherwise make
normalization spin forever. Exceeding it rejects the declaration with a deterministic-timeout message. Stack
depth is bounded by the runtime (`-K2g`).

### The string constructor is read from the environment

Lean hardcodes the constant a string literal expands through, and it changed with `String`'s representation:
`String.mk` up to about Lean 4.20, `String.ofList` since. tenet-hs reads whichever exists, so one build checks
exports from either toolchain. It can only affect what a literal reduces to, never what is accepted without one.

### No acceleration for `Nat.log2`

Like Tenet, tenet-hs does not shortcut `Nat.log2` on literals. The definition unfolds instead, so a term that
depends on a large `log2` is slower here, and never wrong.

## Against Tenet

| | Gap | Effect |
| --- | --- | --- |
| 1 | Reads lean4export NDJSON only; no `.olean` reader | cannot check a module straight from a build directory |
| 2 | Single-threaded | `Init` takes about a minute; Mathlib would take hours |
| 3 | No `TENET_COMPLETE_LEVELS` option | level equality is Lean's, which is the default in Tenet as well |
| 4 | No `--low-memory` or heap sizing | the runtime defaults apply |
| 5 | Slower on the arena's `perf/` tests | two to five times; see [design](design.md#what-was-measured) |

None of these changes a verdict. The first two are the largest practical differences and the next things to
build.
