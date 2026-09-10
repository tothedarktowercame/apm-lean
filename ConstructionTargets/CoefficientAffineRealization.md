# Affine realization with explicit coefficients

For `R : Type` with `[CommRing R]` and a universe-zero index type `ι`
with `[Fintype ι]`, the source is
`CoefficientVertexCone.VertexChains R (stdSimplex ℝ ι)`. The target is
the actual singular chain complex of that standard simplex in `ModuleCat R`,
with coefficient object `ModuleCat.of R R`.

`affineGenerator` assigns an ordered tuple of points in the standard simplex
the singular generator of its affine simplex. The existing coefficient-
independent affine-face equation, combined with the coefficient-generic
singular boundary formula, proves `affineGenerator_boundary`.

`vertexRealizationDegree` is the coproduct descent assigning each ordered
vertex generator its affine generator. `vertexGenerator_vertexRealizationDegree`
proves this assignment as an exact equation of module morphisms. Comparing
the alternating boundaries on both sides proves differential compatibility;
`vertexRealization` packages these degree maps as a chain map. The integer
and rational examples specialize this chain map to the standard one-simplex
indexed by `Fin 2`.

The source exactly promotes `/tmp/CoefficientAffineRealization.lean`, SHA256
`99f50d47774a00c930c11d7c81336f8a6e6eae7cd29a9f7e6828d37d8bd91575`.
Validation includes fixture and canonical compilation, the focused build,
three standard-only printed axiom audits, both coefficient specializations,
and placeholder and scope checks.

Recursive barycentric subdivision and the actual singular subdivision
endomorphism with naturality remain in the parent probe. This packet claims
no subdivision, homotopy, small-chain comparison, excision or frozen closure.
