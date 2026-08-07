# Proof Outline: b95J04

The characteristic obstruction and factorization of `X^p - 1` are complete.
Mathlib's Kummer-extension file supplies most of the forward and converse
machinery needed for the remaining conjunction.

A local helper now proves that every specified nonidentity automorphism in a
group of prime cardinality generates the full group, eliminating the earlier
automorphism-orientation issue.

## Remaining boundary

One sorry remains. The forward direction must convert `α ∉ F` into the
nonexistence of a p-th root in `F`, apply binomial irreducibility, and transport
the splitting-field equivalence to `F⟮α⟯`. The converse must replay Mathlib's
eigenvector construction with the specified generator and assemble all five
properties required by the frozen witness.
