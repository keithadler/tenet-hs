# Security

tenet-hs exists so that a proof does not have to be trusted on one kernel's word. Its security-relevant failure
is **unsoundness**: accepting a declaration that Lean's kernel would reject.

If you find one, please report it privately through GitHub's security advisories for this repository, with the
export file (or the Lean source that produces it) and the name of the declaration. A minimal file is ideal. The
negative corpus in `tests/fixtures/invalid` is the model: each case there was a real or plausible hole, kept as a
permanent regression test, and yours will be too.

Rejecting something Lean accepts is a completeness bug rather than a soundness bug. Please open a normal issue.
