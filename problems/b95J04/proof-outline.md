# Proof Outline: b95J04

The characteristic obstruction and factorization of `X^p - 1` are complete.
Mathlib's Kummer-extension file supplies most of the forward and converse
machinery needed for the remaining conjunction.

A local helper now proves that every specified nonidentity automorphism in a
group of prime cardinality generates the full group, eliminating the earlier
automorphism-orientation issue.

Closer hop 2 adds
`apm_b95J04_exists_eigenvector_of_nonidentity_prime_card`, which replays
Mathlib's minpoly argument and produces a nonzero eigenvector for the exact
specified automorphism with eigenvalue `z`.

## Remaining boundary

One sorry remains. The forward direction must convert `α ∉ F` into the
nonexistence of a p-th root in `F`, apply binomial irreducibility, and transport
the splitting-field equivalence to `F⟮α⟯`. The converse must replay Mathlib's
fixed-field and Galois-correspondence arguments for the proved specified
eigenvector, establishing its p-th power lies in the base-field range, that it
is not itself in that range, and that its adjoin is top.
