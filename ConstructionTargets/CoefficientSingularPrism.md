# Coefficient-general singular subdivision homotopy

This module realizes the reviewed ordered-vertex prism on actual singular
chains. The ring `R : Type` has `CommRing R`, and `X : Type` is an arbitrary
topological space. Both are universe zero. Chains use
`singularChainComplexFunctor (ModuleCat R)` with coefficient object
`ModuleCat.of R R`; no connectedness or nonemptiness is required.

`singularPrismDegree` is constructed by coproduct descent: apply the vertex
prism to the standard vertices, realize affinely, then postcompose with the
singular simplex. `prismFace_transport` uses affine naturality of the vertex
prism and realization. `actual_prism_face` identifies this transport with the
actual simplicial face generator. The boundary and correction equations
reuse `CoefficientVertexPrism` and `CoefficientSingularSubdivision`.

The sign convention is `dT + Td = subdivision - identity`. In composition
order, `singularPrism_identity` states that the prism followed by the
differential, plus the lower correction, equals subdivision minus identity.
The lower correction is explicitly zero in degree zero and is the
differential followed by the previous prism in positive degrees.
`prismComponents` supplies the components of `subdivisionHomotopy`, whose
source is `CoefficientSingularSubdivision.singularSubdivision R` and whose
target is the identity. `degree_zero` separately exports the endpoint equation.

Integer and rational standard-edge equations and seven printed axiom audits
are included. The Lean file is an exact promotion of
`/tmp/CoefficientSingularPrism.lean`, SHA256
`021c6faedc9e50031d64ecfff2a3d15604ebfff810b5301841cbf3b45fdd3237`.

Preservation and eventual smallness, positive-degree small-chain comparison,
relative excision and sphere suspension remain before rational S2 H1/H2.
No smallness, excision, sphere homology or frozen consumer closure is claimed.
