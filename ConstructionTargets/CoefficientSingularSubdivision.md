# Coefficient-general singular subdivision

`CoefficientSingularSubdivision.lean` assembles the degree maps from
`CoefficientBarycentricNaturality` into an actual singular-chain endomorphism.
The coefficient ring `R : Type` has `CommRing R`; all spaces are universe zero.
Chains use `singularChainComplexFunctor (ModuleCat R)` with coefficient object
`ModuleCat.of R R`. No connectedness or nonemptiness is required.

Differential compatibility follows from the ordered-vertex differential,
`CoefficientAffineRealization.vertexRealization`, and the reviewed
subdivided-face transport equation. The existing barycentric recursion,
cone construction and affine-change proofs are reused.

`singularSubdivision` commutes with every differential. Its degree-zero map
is the identity. `generator_formula` expresses its action by subdivision of
the standard ordered vertices, affine realization, and actual singular
postcomposition. `naturality` proves that postcomposition by an arbitrary
continuous map followed by subdivision equals subdivision followed by
postcomposition. The degreewise equation is also exported.

`edge_formula` gives the signed two-edge expression obtained by prepending
the barycenter to the two faces. `edge_boundary` gives the original endpoint
difference. Both formulas specialize to the standard edge over integers and
rationals. Eleven printed axiom audits cover the construction and examples.

The source is an exact promotion of `/tmp/CoefficientSingularSubdivision.lean`
(SHA256 `829767b13270ce19a15269b2cad9775dd2d5178ef8a715c8e124b26c84c3af16`).

Homotopy to identity, preservation and eventual smallness, positive-degree
small-chain comparison, relative excision and sphere suspension remain
before rational S2 H1/H2. This packet does not close a frozen consumer or
provide a coefficient-change theorem.
