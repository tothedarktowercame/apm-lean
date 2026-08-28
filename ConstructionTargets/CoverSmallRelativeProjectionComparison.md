# Cover-small relative projection comparison

For arbitrary `U,V`, this target proves on the cover-small union subcomplex
that the range-subcomplex pushout map, followed by the production map of pairs

`(V,{x : V | x ∈ U}) → (X,U)`,

is exactly the inclusion of those cover-small chains into ambient singular chains
followed by `relativeSingularProjection U`. The proof uses the actual pushout
universal property: the left component is zero and the right component is
projection naturality. A homology-level equation is also provided.

The ambient-cover/open hypotheses enter only in the remaining excision step,
which is not a chain-level inverse: the compiled
`relativeExcisionMap` is proved to induce an isomorphism only in positive
degrees through subdivision. To solve for the right-pair term on homology, the
next target must identify `rightPairToAmbientRelative` with the applicable
`relativeExcisionMap` (including the choice `Z = Vᶜ`) and then use the existing
degree-indexed `IsIso` instance. That exact map equality and inverse homology
transport are not assumed here.
