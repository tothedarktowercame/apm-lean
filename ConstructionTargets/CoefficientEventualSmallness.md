# Eventual smallness of actual coefficient-general chains

For every actual R-valued singular chain c in degree n and every indexed
open cover U, `actual_chain_eventual` constructs a threshold N such that
for every k at least N there is an actual cover-small chain q whose inclusion
is the degree-n application of the k-fold subdivision chain map to c.
The commutative ring R, topological space X and cover index type are universe
zero. Chains use `ModuleCat.of R R`. Every natural-number degree is included;
no connectedness, nonemptiness or finite-cover assumption is imposed.

`subdivisionIterate` constructs chain-map iterates and `subdivisionIterate_f`
identifies their components with `singularSubdivisionIterate`. Affine
realization compatibility and finite iteration equations identify generator
iterates with the coefficient-independent finite geometric formulas.
The existing eventual subordinate-support theorem and finite realization
factorization then provide generator lifts.

`chain_factorization` uses `CoefficientChainSupport.coordinates` to obtain
finite support with arbitrary R coefficients and chooses a common exponent.
It evaluates the generator lifts at those coefficients and sums the resulting
small chains. `eventual_factorization` applies the reviewed restricted
subdivision and its actual inclusion equation to construct preimages at
every larger exponent. No integral-chain conclusion is substituted for an
R-linear statement.

Imports are `CoefficientChainSupport` and `CoefficientSmallPreservation`.
Integer and rational overlapping interval-cover examples quantify over
arbitrary chains in every degree. Eight printed axiom audits are included.
The Lean file is an exact promotion of `/tmp/CoefficientEventualSmallness.lean`,
SHA256 `58ac8aa7368bfb5e6d25f0bd6e9ac8cf8d56540ff6b59030b03f6723e99ef15e`.

Positive-degree small-chain homology comparison, relative excision and sphere
suspension remain before rational S2 H1/H2. This module claims no homology
isomorphism or frozen consumer closure.
