# ConcatSubdivisionShrinkingFold

This target defines `shrinkingPrefixObject`, `shrinkingPrefixArrow`, and
`shrinkingPrefixFold` directly from the actual concatenated chain. The two
endpoint lemmas align every restricted segment with its restricted vertices,
and the arrow definition retains both resulting `eqToHom` transports.

The first remaining theorem is the zero-stage comparison. Its literal goal is
`composeFin (shrinkingPrefixObject D S T 0) (shrinkingPrefixArrow D S T 0) =
composeFin (D.obj ∘ concatSubdivision.point) concatSubdivision.mappedPiece`.
Although both embeddings preserve `Fin.val`, their dependent endpoint proof
fields differ, so simplification does not identify the arrow families. It must
use `composeFin_reindex_of_index_eq` with an explicit zero-stage index equality.

The successor theorem must then compare the stage-`r+1` object family
with the `Fin.castSucc` restriction of stage `r`, then transport the final
stage-`r` arrow using `shrinkingSegment_last_eq_rightSegment`. This is a
one-arrow recurrence; `composeFin_dropLast_two` alone removes two arrows and
therefore cannot establish it without pairing stages or adding a one-arrow
restricted-prefix reindex theorem. No suffix split is claimed here.
