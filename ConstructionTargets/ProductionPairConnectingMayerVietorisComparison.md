# Production pair connecting-map comparison

This target transports the connecting map of the direct cokernel presentation
of a topological pair to the existing production `singularPairConnecting`.
The comparison is obtained from the compiled
`singularPairShortComplexIsoCokernel` and Mathlib's connecting-map naturality.
It also records the absolute-to-relative projection normalization on homology.

Together with `PairConnectingMayerVietorisComparison`, this establishes the
categorical sign and the direct-cokernel-to-pair representation square. It does
not yet identify an open-cover range-subcomplex cokernel with a topological
pair. The first remaining coherence is an explicit chain-level square for the
nested subtype homeomorphism

`{x : V | x.1 ∈ U} ≃ (U ∩ V : Set X)`

and the corresponding ambient comparison between the range of `U ∪ V` and
the chosen union subtype. That square is needed before the pushout map
`unionToRightRelative` can be identified with the actual pair projection
followed by inverse excision. Neither that identification nor a sphere sign
recurrence is assumed here. The frozen `t94J08` statement remains false in
dimension zero.
