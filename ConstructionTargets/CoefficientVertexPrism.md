# Coefficient-general ordered-vertex prism

This module constructs a recursive prism on actual ordered-vertex chains in
`ModuleCat R`, with coefficient object `ModuleCat.of R R`. The commutative
ring and simplex index types are universe zero; simplex index types have
`Fintype` instances.

`vertexPrism` is zero in degree zero. In positive degree, coproduct descent
extends the generator formula: cone off the difference between subdivision
and identity after subtracting the previous prism correction. This reuses
`CoefficientVertexCone`, the subdivision from `CoefficientBarycentricNaturality`,
and the vertex maps from `CoefficientAffineNaturality`, imported through
`CoefficientSingularSubdivision`.

`vertexPrism_identity` proves that the prism followed by the differential,
plus `vertexPrismCorrection`, equals subdivision minus identity. The
correction is zero in degree zero and the differential followed by the
previous prism in positive degree. The proof uses the cone boundary equation,
the subdivision differential equation and induction.

`vertexPrism_natural` proves compatibility with vertex functions preserving
barycenters. `vertexPrism_affine_natural` establishes that hypothesis for
affine simplex maps using the existing geometric barycenter formula.
Integer and rational standard-edge identities and five printed axiom audits
are included.

The Lean file is an exact promotion of `/tmp/CoefficientVertexPrism.lean`,
SHA256 `09c3a742f6c44c3c93272a41faf3de451bd14b1e5924cc8229a57e5bc9f2b287`.

Realization on actual singular chains, singular face transport and the
correctly oriented `Homotopy` from subdivision to identity remain downstream.
This module does not establish a singular-chain homotopy, small-chain
comparison, excision or frozen consumer closure.
