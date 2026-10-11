# How tenet-hs is built, and why

tenet-hs is about 4,700 lines of Haskell with no dependencies beyond the libraries that ship with GHC
(`base`, `containers`, `bytestring`, `text`, `mtl`, `array`). It is a port of the *design* of
[Tenet](https://github.com/keithadler/tenet), which in turn follows Lean's kernel, into a language that has very
different strengths: no mutation by default, a lazy evaluator, and a garbage collector that copies. This page is
about the places where that mattered.

## The shape of it

```
 lean4export NDJSON
        |
   Tenet.Json -> Tenet.Export          lines -> names, levels, expressions, declarations
        |
   Tenet.Check                          replay in order, report, compare the exporter's claims
        |
   Tenet.Add                            check one declaration, add its constants, roll back on rejection
      /        |         \
 Quot      Inductive     (definitions, theorems, axioms, opaque, mutual)
      \        |         /
   Tenet.TypeChecker                    infer, whnf, isDefEq, primitives
        |
   Tenet.Expr  Tenet.Level  Tenet.Name  Tenet.ExprOps  Tenet.HTable  Tenet.Env
```

The checker is a record of mutable caches (`TC`) passed explicitly, and every operation that can reject lives in
`IO` and rejects by throwing a `KernelError`. That is the opposite of idiomatic Haskell, on purpose. A kernel
that threads a `State` monad through `whnf` and `isDefEq` pays for it on every call, and the algorithm is full of
things that want to be a mutable table or an early exit.

## Terms

`Tenet.Expr` is a plain sum type, but each node carries a record of facts computed once, at construction:

| Cached | Used for |
| --- | --- |
| a structural hash | cheap inequality, bucket choice in every table |
| the range of loose bound variables | substitution skips any subterm that has none |
| "mentions a free variable" | `instantiate` and friends skip closed terms; reflection only fires on closed terms |
| "mentions a universe parameter" | level instantiation skips terms without any |
| node count, saturating | decides which subterms are worth memoizing |

The constructors are exposed only as bidirectional pattern synonyms (`App f a`, `Lam n bi d b`, and so on), so
code reads like a normal data type while every node is built through a smart constructor that fills the cache.

**Equality ignores binder names and annotations**, as the kernel's does. It is structural, with a pointer-equality
fast path and a hash check before any recursion. Terms in this kernel are heavily shared DAGs, and comparing two
equal copies node by node is exponential in the depth of the sharing, so large pairs that are not pointer-equal
are compared with a table of the pairs already visited, as Lean's `expr_eq_fn` does. A revisited pair is assumed
equal, which is sound because any inequality aborts the whole comparison. That uses `unsafeDupablePerformIO`
around a table that never escapes the call, which is safe: the function is pure from outside.

## Substitution

Instantiating, abstracting, lifting and lowering bound variables are all one function, `replaceIO`, with a
callback that sees each subterm and the number of binders above it. It memoizes by (subterm, binder depth) in a
mutable hash table, and only for subterms above a small size, because a small shared subterm is cheaper to
rebuild than to look up and cannot blow up. The pure variant `replaceE` runs the same code under
`unsafeDupablePerformIO`. The inductive module needs the effectful one, because eliminating nested occurrences
inspects the environment while it rewrites.

## Caches

Every cache is `HTable` (`src/Tenet/HTable.hs`): a small mutable table with chained buckets, where the caller
supplies each key's hash and the equality test. It exists because of measurements, below.

## Fresh variables

Free variables are integers from a global counter, so identities are unique across checkers and a local context
only ever grows. A checker holds an `IORef` to an `IntMap` of declarations, and the inductive module shares one
context across the several short-lived checkers it creates, as Tenet does.

## Declarations roll back

`addDecl` snapshots the environment, tries the declaration, and restores the snapshot on rejection. The
environment is a persistent map inside an `IORef`, so the snapshot is free. A child environment, used to stage
the auxiliary types of a nested inductive and to re-derive a block the exporter already wrote, is the same map
copied with a fresh list of its own constants.

The first attempt runs with failure caching on. Caching *failed* definitional-equality results can only make the
checker stricter, since definitional equality is not transitive, so it can reject more but never accept more.
A declaration rejected that way is re-run with the cache off, and the reference algorithm's verdict is the one
reported. Nothing about this is observable from outside except speed.

## Why single-threaded

Checking order matters: a declaration's constants are visible only after it is accepted, which is what makes a
theorem unable to prove itself. Tenet gets parallelism by adding every constant first and checking declarations
out of order, with extra guards for the cases that creates. tenet-hs does not, yet. The arena's scoring counts
instructions retired, not wall time, so parallelism would help a table of timings and not the number that
matters there.

## What was measured

Profiling decided most of this, and some of it contradicted what looked obvious.

**Substitution first.** The first correct build spent about 75% of its time in `replaceE` and the `IntMap` that
memoized it, and allocated 43 GB on one test. Replacing the persistent map with a mutable table
([`HTable`](../src/Tenet/HTable.hs)) and memoizing only larger subterms roughly halved `app-lam` (15.7 s to 7.8 s)
and took all of `Init` from 67 s to 52 s.

**Equality second.** `cacheGet` was 16% of a profile with almost no allocation, which means expensive
comparisons and not expensive lookups: two equal terms built separately were compared node by node. The
visited-pair table above fixed that.

**Hash-consing, tried and reverted.** Interning every term so that equality is an integer compare is the obvious
answer to the above, and it works well in the JVM. In Haskell, on these inputs, it was a net loss, by a lot:

| `perf/` test | before | hash-consed |
| --- | --- | --- |
| `app-lam` | 7.8 s | 85 s |
| `beta-ladder` | 2.4 s | 15.6 s |
| `magma-list-deep-n21` | 6.4 s | 11.6 s |
| `magma-list-pair-n7` | 4.0 s | 10.4 s |

The cost was the table probe on construction. These tests build roughly 140 million nodes, and with hash-consing
every one of the large ones pays a hash lookup into a table too big for cache, where before a transient node cost
one allocation and was gone. Restricting interning to larger and larger terms moved the cost around without
removing it: at a threshold of 12 nodes the probe was 33% of the profile, and above that, equality on the
terms that were no longer interned fell back to structural comparison. Memoized structural equality beat both.
The lesson is specific to this workload, where most terms are short-lived intermediates; it says nothing about a
checker whose terms mostly live long.

**The collector.** About half the wall time on the heavy tests is garbage collection, because the checker's
caches keep everything alive and a copying collector copies live data. A larger nursery recovers 15 to 25%
(`-A256m` takes `magma-list-deep-n21` from 6.2 s to 5.2 s) but the arena also scores peak memory, so the default
stays at `-A64m`.

For scale: Tenet checks the same `perf/` tests two to five times faster. The remaining gap is mostly allocation
and collection, and it is the main thing left to work on.

## Where the unsafe parts are

Two uses of `unsafeDupablePerformIO` (the pure `replaceE`, and the large-term `Eq`), one of `unsafePerformIO`
(the global counter that numbers free variables), and `reallyUnsafePtrEquality#` as a fast path in equality and in
"did substitution change anything". None of them can change a result: the first two are pure from outside, the
counter only needs to be unique, and the pointer test can only report "different" for terms that are equal, which
costs time and never correctness.
