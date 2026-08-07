# Proof Outline: b95J02

The finite-abelian-group half is complete using Mathlib's group exponent.
For the operator half, the universal bound
`natDegree (minpoly F T) ≤ finrank F V` is proved from divisibility by the
characteristic polynomial.

A local helper further proves that equality of these degrees forces
`T.charpoly = minpoly F T`.

## Remaining boundary

One sorry remains for the cyclic-vector equivalence. The reverse direction is
now precisely the classical theorem that a nonderogatory operator admits a
cyclic vector. Mathlib has no packaged Krylov/rational-canonical-form theorem
providing this implication; the forward direction likewise needs the cyclic
module quotient and annihilator dimension calculation assembled locally.
