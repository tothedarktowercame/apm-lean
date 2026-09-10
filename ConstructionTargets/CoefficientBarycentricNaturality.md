# Barycentric subdivision and affine changes with explicit coefficients

The coefficient ring `R : Type` has `[CommRing R]`. All spaces and vertex
index types are universe zero; standard-simplex index types have `Fintype`.
Chains use the actual coefficient object `ModuleCat.of R R`.

`vertexSubdivision` is recursively constructed on ordered-vertex chains:
degree zero is identity; a generator in degree `n+1` is sent to its boundary,
then the degree-`n` subdivision, then the cone at its barycenter. The two
generator equations expose this recursion. The cone boundary identities
prove `vertexSubdivision_comm_d`, with the degree-one case handled explicitly
and higher degrees using the vanishing of two consecutive differentials.

`vertexMapDegree_cone` proves compatibility of a vertex map with coning at
the mapped vertex. Induction then proves `vertexSubdivision_natural` for
functions between standard simplices satisfying the stated barycenter-
preservation equation. This equation is a hypothesis of general vertex
naturality, and is proved for affine simplex maps using the existing affine
barycenter geometry. The resulting affine-change equality goes from
subdivision followed by vertex-map to vertex-map followed by subdivision.

Combining that equality with the reviewed affine-realization square and
actual singular postcomposition gives `subdividedFace_transport`.
`degree` is a constructed map in each singular-chain degree: on a singular
generator it subdivides the standard ordered vertices, realizes, and
postcomposes with that singular simplex. `generator_degree` states this
formula. `actual_subdivided_face` identifies the transported realized face
with the actual singular face generator followed by `degree`. Integer and
rational standard-edge examples quantify over both faces `i : Fin 2`.

The source exactly promotes `/tmp/CoefficientBarycentricNaturality.lean`,
SHA256 `551b41e6fb552150000bbedde369c9981b0d038afdb2fd5e4385d990a0c4cf7f`.
Validation includes fixture and canonical compilation, the focused build,
eight standard-only printed axiom audits including the two edge examples,
and placeholder and scope checks.

The singular degree maps are not yet packaged as a chain endomorphism.
Singular differential compatibility, naturality, degree-zero identity and
the complete singular subdivision packet remain to be assembled. Homotopy,
smallness, positive-degree comparison, excision and rational sphere H1/H2
remain downstream. No homology isomorphism or frozen closure is claimed.
