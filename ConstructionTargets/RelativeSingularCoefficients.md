# Relative singular chains with explicit coefficients

The construction uses `R : Type` with `[CommRing R]` and `X : Type` with
`[TopologicalSpace X]`, both in universe zero, and an arbitrary subset
`A : Set X`. No nontriviality, compactness, finiteness or extra categorical
hypotheses are required. Singular chains take values in `ModuleCat R` with
coefficient object `ModuleCat.of R R`.

`singularSubspaceMap` is the chain map induced by the existing geometric
subtype inclusion. The existing injectivity theorem for its map on singular
simplices proves degreewise monomorphisms through the coefficient-generic
coproduct API. `singularSubspaceMap_degree_injective` identifies these with
injective underlying R-linear maps, and `singularSubspaceMap_mono` proves
monicity of the chain map itself.

`relativeSingularSubcomplex` is the categorical image of this actual map.
Its inclusion's chain-map equation explicitly proves that the differential
restricts. `RelativeSingularChains` is the cokernel of the image inclusion,
and `relativeSingularProjection` is its canonical quotient projection.
`relativeSingularChainsIsoCokernelSubspaceMap` identifies this quotient with
the direct cokernel of the original subspace map.

`singularPairShortComplex` uses actual subspace chains on the left, absolute
chains in the middle and the constructed image quotient on the right.
`singularPairShortComplexIsoCokernel` identifies the direct-cokernel short
complex with this presentation, using identity maps on the first two terms
and the inverse of the quotient comparison on the third. Short exactness
follows from the proved monomorphism and cokernel exactness. Thus the proved
sequence is `C_*(A;R) → C_*(X;R) → C_*(X,A;R)` with the actual inclusion
and projection, rather than supplied exactness data.

The integer and rational examples use the literal complex closed unit disk
and its boundary subset `{x | norm x.val = 1}`. Both instantiate the same
generic short-exactness theorem.

The source exactly promotes `/tmp/RelativeSingularCoefficients.lean`, SHA256
`337da567d23409921c88c30c154f68ee37e8e0b27537a492603c1deb828b00c6`.
Validation includes fixture and canonical compilation, the focused build,
seven printed standard-only axiom audits, and placeholder and scope checks.

Connecting morphisms, pair long-exactness, coefficient-general excision,
sphere suspension and endpoints remain downstream, followed by the exact
rational S2 comparisons. This packet supplies no coefficient comparison,
positive-dimensional sphere table or frozen consumer closure.
