# The export format tenet-hs reads

tenet-hs consumes the NDJSON export written by [lean4export](https://github.com/leanprover/lean4export), format
major version 3. The authoritative description is lean4export's `format_ndjson.md`; this page records what
tenet-hs relies on and the variations it accepts.

## Structure

One JSON object per line. The first is `{"meta": …}` with exporter, Lean and format versions. Then, in
dependency order, three kinds of table entries and the declarations:

| line | meaning |
| --- | --- |
| `{"in": i, "str": {"pre": p, "str": s}}`, `{"in": i, "num": {"pre": p, "i": n}}` | name `i` is prefix `p` extended by a string or a number; name 0 is anonymous |
| `{"il": i, "succ": l}`, `"max"`, `"imax"`, `"param"` | level `i`; level 0 is zero |
| `{"ie": i, "bvar": n}`, `"sort"`, `"const"`, `"app"`, `"lam"`, `"forallE"`, `"letE"`, `"proj"`, `"natVal"`, `"strVal"`, `"mdata"` | expression `i` |
| `{"axiom": …}`, `{"def": …}`, `{"thm": …}`, `{"opaque": …}`, `{"quot": …}`, `{"inductive": …}` | a declaration |

Things the reader relies on, each learned from a file that exercised it:

- **Indices need not be dense or in order.** An entry may be defined at any index, as long as everything it
  refers to is already defined; defining an index twice is an error. The arena's `sparse-name-index` and
  `level-index-out-of-order` tests are about exactly this.
- **`mdata` is dropped.** Metadata has no effect on type checking.
- **`natVal` is a string**, because the numbers can exceed any machine integer.
- **Levels are kept raw.** `max` and `imax` are not simplified on reading, so a file's level terms are the ones
  the kernel normalizes.
- **`let` loses its `nondep` hint.** lean4export normalizes the flag to `false`, and equality ignores it.

## Declarations

- `def` carries `hints` (`"opaque"`, `"abbrev"` or `{"regular": height}`) and `safety` (`"safe"`, `"unsafe"`,
  `"partial"`). An array of more than one `def` is a mutual block, which the kernel accepts only when it is
  unsafe or partial.
- `inductive` is a whole mutual block: the types, all constructors, and all recursors with their computation
  rules, as Lean's kernel produced them. tenet-hs uses only the types and constructors as input and treats the
  rest as a claim to verify: it derives the constructors' metadata and the recursors itself and compares every
  field.
- `quot` lines carry the four quotient constants; tenet-hs builds them and compares.

## 3.0 versus 3.1

| | 3.0 | 3.1 |
| --- | --- | --- |
| inductive block fields | `inductiveVals`, `constructorVals`, `recursorVals` | `types`, `ctors`, `recs` |
| `def`, `thm`, `opaque`, `axiom` | one-element arrays | objects with an `all` field |
| `numNested` on inductive types | present | present |

Both are accepted. Both fixtures in [`tests/fixtures`](../tests/fixtures) are checked on every `cabal test`.
