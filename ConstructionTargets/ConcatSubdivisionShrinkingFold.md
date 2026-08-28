# ConcatSubdivisionShrinkingFold

This target defines `shrinkingPrefixObject`, `shrinkingPrefixArrow`, and
`shrinkingPrefixFold` directly from the actual concatenated chain. The two
endpoint lemmas align every restricted segment with its restricted vertices,
and the arrow definition retains both resulting `eqToHom` transports.

`conjugatedArrow_compose` is the generic endpoint coherence theorem: two
successive, independently generated pairs of `eqToHom` transports equal one
supplied composite pair after index equalities are eliminated.
`whisker_conjugatedArrow_compose` preserves that equality under explicit
left and right composition.  This is the reusable form needed when an arrow
already carries one pair of endpoint transports and a reindexing contributes
another pair outside it.

`shrinkingPrefixFold_zero` applies that theorem pointwise and then uses
`composeFin_reindex_of_index_eq`. It identifies stage zero with the full
concatenated fold while retaining the two outer identity-coordinate
isomorphisms returned by the generic reindex theorem.

The successor theorem must then compare the stage-`r+1` object family
with the `Fin.castSucc` restriction of stage `r`, then transport the final
stage-`r` arrow using `shrinkingSegment_last_eq_rightSegment`. This is a
one-arrow recurrence; `composeFin_dropLast_two` alone removes two arrows and
therefore cannot establish it without pairing stages or adding a one-arrow
restricted-prefix reindex theorem. No suffix split is claimed here.
