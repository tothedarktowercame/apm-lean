# Coefficient-general small-chain homology comparison

For a commutative ring R and an arbitrary indexed open cover U of X,
`homologyIso` constructs an isomorphism from homology of actual cover-small
chains to homology of actual singular chains in every natural-number degree.
Both complexes use coefficient object `ModuleCat.of R R`. R, X and the cover
index type are universe zero. No connectedness, nonemptiness or finite-cover
hypothesis is imposed; cycles and bounding chains have arbitrary R coefficients.

`elementHom`, `cycle_lift` and `exists_boundary` connect actual elements with
categorical cycles and boundaries in `ChainComplex (ModuleCat.{0} R) Nat`.
Positive-degree surjectivity subdivides a representative cycle until it has
a small-chain preimage. The monic inclusion shows that preimage is a cycle;
the absolute iterated homotopy preserves its homology class. Injectivity
subdivides an actual bounding chain, transfers its boundary using the iterate
inclusion equation, and applies identity action of restricted iterates on
homology. The reviewed `CoefficientSmallH0` result supplies degree zero.

`homologyIso_hom` identifies the forward arrow exactly with
`HomologicalComplex.homologyMap` of the actual cover-small inclusion.
`inverse_left` states inverse followed by that map is identity;
`inverse_right` states that map followed by inverse is identity.
The module imports `CoefficientIteratedHomotopy` and reuses eventual
factorization and absolute/restricted homotopies, without assuming comparison
or reinterpreting an integral theorem over R.

All-degree integer and rational interval-cover examples and eight printed
axiom audits are included. The Lean file is an exact promotion of
`/tmp/CoefficientSmallComparison.lean`, SHA256
`d70b14c6d71ccbf4c9bcdea7613261413bfa3f68457aa3bac1fcdfb2b52f16dc`.

Coefficient-general relative excision and sphere suspension remain before
rational S2 H1/H2. This module claims no relative-excision theorem, sphere
homology calculation or frozen consumer closure.
