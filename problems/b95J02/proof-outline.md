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
now narrowed by `Module.exists_ker_toSpanSingleton_eq_annihilator`: applied to
the finite torsion polynomial module `Module.AEval' T`, it supplies a vector
whose annihilator equals the whole module annihilator. Together with
`Polynomial.span_minpoly_eq_annihilator`, this gives the correct candidate
without rational canonical form. It remains to prove that a relation among
the first `finrank F V` orbit vectors yields a polynomial of degree strictly
below the minimal polynomial in its principal ideal, hence zero; finite
cardinality then promotes those vectors to a basis. The forward direction's
annihilator identification is already supplied by the closer-hop-2 helper.
