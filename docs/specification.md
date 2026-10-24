# What the kernel decides, rule by rule

This is the kernel written as a list of rules, each next to the function that implements it, so the code can be
read against the type theory and not only against itself. The rules are those of Lean 4's kernel; for the theory
behind them see Mario Carneiro's thesis [The Type Theory of Lean](https://github.com/digama0/lean-type-theory/releases)
and Chris Bailey's book [Type Checking in Lean4](https://ammkrn.github.io/type_checking_in_lean4/).

Everything named here is in [`src/Tenet/TypeChecker.hs`](../src/Tenet/TypeChecker.hs) unless another module is given.

## Typing

`Γ ⊢ e : T`, one case per syntactic form, from `inferTypeCore` and its helpers. Checking (`inferOnly = False`)
also validates sub-terms; inference (`inferOnly = True`) trusts them and is used wherever a term is already
known to be well typed.

| Rule | Statement | Function |
| --- | --- | --- |
| Sort | `⊢ Sort u : Sort (u+1)`, and `u` mentions only declared level parameters | `inferTypeCore`, `checkLevel` |
| Constant | `⊢ c.{v̄} : T[ū := v̄]` for `c : T` declared with parameters `ū`, with the right number of levels | `inferConstant` |
| Free variable | `Γ, x : A ⊢ x : A` | `inferTypeCore` |
| Application | `f : (x : A) → B`, `a : A'`, `A ≡ A'` gives `f a : B[x := a]` | `inferApp` |
| Lambda | `Γ, x : A ⊢ b : B` gives `(fun x : A => b) : (x : A) → B` | `inferLambda` |
| Pi | `A : Sort u`, `B : Sort v` gives `((x : A) → B) : Sort (imax u v)` | `inferPi` |
| Let | `v : A`, `b : B` with `x : A := v` in scope gives `(let x : A := v; b) : B[x := v]` | `inferLet` |
| Projection | `e : S ā` for a structure `S` gives `e.i : ` the `i`-th field type, earlier fields projected | `inferProj` |
| Literal | a natural number literal has type `Nat`, a string literal `String`, if the environment's `Nat` and `String` are what the literals mean | `inferLit`, `checkPrimitive` |
| Unsafe and partial | a safe declaration may not mention an unsafe or partial constant | `inferConstant` |

A loose bound variable reaching the checker is an error: terms are opened with free variables first.

## Reduction

`e ↝ e'`, from `whnfCoreX` (no unfolding) and `whnf` (with unfolding and literal arithmetic).

| Rule | Statement | Function |
| --- | --- | --- |
| Beta | `(fun x => b) a ↝ b[x := a]` | `whnfCoreX`, `betaRev` (`Tenet.ExprOps`) |
| Zeta | `(let x := v; b) ↝ b[x := v]`, and a let-bound free variable reduces to its value | `whnfCoreX` |
| Delta | `c.{v̄} ↝` its value, for a definition or theorem | `whnf`, `unfoldDefinition` |
| Iota | `I.rec … (I.ctor_i ā) ↝` the rule for `ctor_i`, applied to the parameters, motives, minors and fields | `tryReduceRec` |
| K | for an inductive proposition with one constructor and no fields, a major premise whose type is that proposition is replaced by the constructor, even when it is a variable | `toCtorWhenK` |
| Structure eta in iota | a major premise of a structure type is expanded to the constructor applied to its projections | `toCtorWhenStructure`, `expandEtaStruct` |
| Projection | `(S.mk ā).i ↝ aᵢ` | `reduceProjCore` |
| Quotient | `Quot.lift f h (Quot.mk r a) ↝ f a` and `Quot.ind h (Quot.mk r a) ↝ h a` | `quotTryReduceRec` |
| Nat literals | `Nat.add`, `sub`, `mul`, `div`, `mod`, `gcd`, `pow`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight` on literals computed directly; `Nat.succ` of a literal; `Nat.beq` and `Nat.ble` to a `Bool` | `reduceNat` |
| Literal to constructor | a `Nat` literal in a major premise becomes `Nat.zero` or `Nat.succ n`; a string literal becomes a list of characters | `natLitToConstructor`, `stringLitToConstructor` |
| Native | `Lean.reduceBool` and `Lean.reduceNat` need compiled code; for exports from Lean 4.34 and earlier (or a Lean it cannot identify) the checker declines; for 4.35 and later the rule does not exist in Lean's kernel and the terms are ordinary constants, so a proof that needs them is rejected | `reduceNative` |

Each literal shortcut is taken only if the constant it is named after has been checked against its defining
equations; see [divergences](divergences.md#an-accelerated-primitive-is-checked-before-it-is-trusted).

## Definitional equality

`Γ ⊢ t ≡ s`, from `isDefEqCore` and its helpers. The order matters, because each step is sound and the
algorithm is incomplete by design (definitional equality is not transitive in the algorithmic sense).

| Order | Rule | Function |
| --- | --- | --- |
| 1 | Syntactically equal up to binder names and annotations | `quickIsDefEq`, `Eq Expr` (`Tenet.Expr`) |
| 2 | Same binder kind: domains equal, then bodies equal under a fresh variable | `isDefEqBinding` |
| 3 | `Sort u ≡ Sort v` when `u` and `v` are equal after level normalization | `quickIsDefEq`, `isEquiv` (`Tenet.Level`) |
| 4 | Literals equal | `quickIsDefEq` |
| 5 | A closed term against `Bool.true` is reduced fully (proofs by reflection) | `isDefEqCore` |
| 6 | Weak head normalize both sides without delta, projections cheaply | `whnfCoreX` |
| 7 | Proof irrelevance: two proofs of the same proposition are equal | `isDefEqProofIrrel` |
| 8 | Lazy delta: unfold the side with the greater reducibility height, or both; same-head applications try their arguments first | `lazyDeltaReduction`, `lazyDeltaReductionStep` |
| 9 | Nat offsets: `n+1 ≡ m+1` reduces to `n ≡ m`, and literals count as offsets | `isDefEqOffset` |
| 10 | Equal constants with equivalent levels; the same free variable | `isDefEqCore` |
| 11 | Two projections of the same field are compared by unfolding the structures they project from | `lazyDeltaProjReduction` |
| 12 | Weak head normalize again, now with full reduction of projections | `isDefEqCore` |
| 13 | Congruence on applications | `isDefEqApp` |
| 14 | Eta for functions: `f ≡ fun x => f x` | `tryEtaExpansion` |
| 15 | Eta for structures: `s ≡ S.mk s.1 … s.n` | `tryEtaStruct` |
| 16 | A string literal against the string constructor applied to a list | `tryStringLitExpansion` |
| 17 | Unit-like types: any two elements of a one-constructor type with no fields are equal | `isDefEqUnitLike` |

## Universe levels

`Tenet.Level`. Levels are `zero`, `succ`, `max`, `imax` and parameters. Two levels are equal when they are equal
after `normalize` (`isEquiv`); `isGeq` is the sound, incomplete order used by the inductive checks. As in Lean,
level equality is decided by normalizing once, so a few pairs that are semantically equal are not settled; see
[divergences](divergences.md).

## Declarations

`Tenet.Add` checks and adds each kind, and `Tenet.Quot` and `Tenet.Inductive` do the two that derive constants.

| Declaration | What is checked |
| --- | --- |
| Axiom | name is new, no duplicate level parameters, no free variables, type is a type |
| Definition | the axiom checks, then the value has the declared type; unsafe definitions are added before their bodies are checked, so they may recurse |
| Theorem | as a definition, and the type is a proposition |
| Opaque | as a definition, with a safe checker whatever the flag says |
| Mutual definitions | unsafe or partial only, one safety and one set of level parameters, headers checked, all added, then each body checked |
| Quotient | `Eq` has exactly its expected shape, then the four constants are built with their fixed types |
| Inductive | see below |

### Inductive types

`Tenet.Inductive.addInductive` follows the kernel's `add_inductive`:

1. every occurrence of a block type in a constructor is applied to exactly the block's parameters and levels;
2. nested occurrences (`List (Tree α)`) are replaced by auxiliary types in `_nested.*`, making an ordinary mutual
   block;
3. the types agree on parameters and live in one universe;
4. each constructor takes the parameters, has fields that fit the universe (unless the type is a proposition), is
   strictly positive (unless unsafe), and returns the type;
5. the elimination universe is `Prop` only if the type is a proposition that cannot eliminate into `Type`
   (more than one constructor, mutual, or a non-`Prop` field that is not in the result type);
6. the recursor types and computation rules are built, the `K` flag set for one-constructor propositions with no
   fields, and each rule is checked to preserve types;
7. for a nested block, the auxiliary types are rewritten back to the originals and everything is re-checked.

The exporter's constructors and recursors are never trusted. They are compared, field for field, with what the
kernel derived; see [Keeping it honest](#keeping-it-honest).

## Keeping it honest

Every rule above is exercised by Lean's own library and by hostile inputs, and `docs/testing.md` says how.
A rule that no input reaches is a rule whose correctness nothing has shown, however many declarations passed
through the checker. Rule-coverage counting, which Tenet has, is not yet implemented here (see
[the status page](status.md#not-done-yet)).
