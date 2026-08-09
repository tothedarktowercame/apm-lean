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

Closer hop 3 adds `apm_b95J04_eigenvector_is_radical_generator`. It proves
that eigenvector is outside the algebra-map range, its `p`-th power belongs to
the range by the finite Galois fixed-field theorem, and its adjoin is top by
injectivity of the Galois correspondence. The complete converse is now wired
into the main theorem without sorry.

## Remaining boundary

One sorry remains, confined to the forward direction. It must convert `α ∉ F` into the
nonexistence of a p-th root in `F`, apply binomial irreducibility, and transport
the splitting-field equivalence to `F⟮α⟯`, including the separate quadratic
case because Mathlib's prime-power irreducibility criterion assumes an odd
prime.

## Hop 4 bridge statements

- `apm_b95J04_bridge_radical_irreducible` converts a non-base element
  `alpha` satisfying `alpha ^ p = a` into irreducibility of
  `X ^ p - C a` for prime `p`.
- `apm_b95J04_bridge_radical_adjoin_galois` packages the remaining Kummer
  construction on the concrete subtype `F⟮alpha⟯`: Galoisness, the cyclic
  group equivalence, and its exact action on the distinguished radical.

Given the original range witness for `alpha ^ p`, the first bridge supplies
the irreducible polynomial and the second produces exactly the forward
conclusion. The converse remains fully compiled from closer hop 3.
