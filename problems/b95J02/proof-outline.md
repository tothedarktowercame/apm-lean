# Proof Outline: b95J02

The finite-abelian-group half is complete using Mathlib's group exponent.
For the operator half, the universal bound
`natDegree (minpoly F T) ≤ finrank F V` is proved from divisibility by the
characteristic polynomial.

A local helper further proves that equality of these degrees forces
`T.charpoly = minpoly F T`.

Closer hop 2 adds
`apm_b95J02_aeval_eq_zero_of_cyclic_vector`: when the orbit of `v` spans,
any polynomial satisfying `p(T)v = 0` has `p(T) = 0`. The proof uses
commutativity of polynomial evaluations and extends vanishing from the orbit
through its span.

## Remaining boundary

One sorry remains for the cyclic-vector equivalence. The reverse direction is
now precisely the classical theorem that a nonderogatory operator admits a
cyclic vector. Mathlib has no packaged Krylov/rational-canonical-form theorem
providing this implication; the forward direction likewise needs the cyclic
The annihilator-identification part of that forward direction is now proved;
only its finite-dimensional degree calculation remains.
