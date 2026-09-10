# Naturality of affine realization with explicit coefficients

The coefficient ring `R : Type` has `[CommRing R]`. Vertex types are
universe-zero types; arbitrary functions between them require neither
topology nor finiteness. `vertexMapDegree` constructs their maps on ordered-
vertex chains by coproduct descent with coefficient object `ModuleCat.of R R`.
Its generator equation and compatibility with the alternating differential
construct `vertexMap`. Coproduct extensionality proves its identity and
composition laws.

For affine maps between standard real simplices, the target index type has
`Fintype` and the source is indexed by `Fin (m+1)`. The coefficient-independent
affine composition formula identifies realized mapped generators with the
actual singular postcomposition of realized generators. The degreewise
lemma `vertexRealization_affine_natural` states realization then singular
postcomposition equals vertex-map then realization. `realization_naturality`
uses its symmetry to give the requested chain-map equation:

`vertexMap (affineSimplex u) ≫ target realization = source realization ≫ singularPostcomposition (affineSimplex u)`.

`face_naturality` specializes this equation to affine face maps.
`affine_face_eq` identifies those maps with `stdSimplex.map i.succAbove`,
so `actual_face_naturality` is the equation for the actual face inclusion.
Integer and rational examples range over both faces `i : Fin 2` of the
standard edge. All source, target and postcomposition maps retain the same
explicit coefficient object.

The source exactly promotes `/tmp/CoefficientAffineNaturality.lean`, SHA256
`2e697058de2561b9c7de96a85018a508c5a0ca054983a4459dab09ba042c7800`.
Validation includes fixture and canonical compilation, the focused build,
six standard-only printed axiom audits, integer/rational edge-face examples,
and placeholder and scope checks.

Subdivision affine-change compatibility and the remaining `MissingFaceTransport`
assembly still precede singular differential compatibility. This packet proves
no singular subdivision chain endomorphism, homotopy, smallness, excision,
change-of-coefficients isomorphism or frozen closure.
