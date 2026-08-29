# Two-open descent object reconstruction

`canonicalTwoOpenDescentDatum F` restricts an ambient functor `F` along the
two subtype inclusions. Its common object coordinate is literally
`F.obj ⟨x⟩`. The overlap equation is proved from
`map_pathInPiece_coverPieceInclusion`: mapping either subtype lift of an
overlap path back into the ambient space gives the original path class.

`map_pathConcat_eq_composeFin` proves by finite induction that a functor maps
`Path.concat` to the repository's dependent `composeFin`. The theorem
`canonical_mappedPiece` identifies every canonical subdivision piece with the
original ambient functor map, and `canonical_composeFin` telescopes those
identifications.

`canonical_evaluate` then uses `quotient_concat_eq` and explicit endpoint-cast
unbracketing to show that evaluation of any subordinate subdivision is exactly
the original map of the represented path. `canonicalReconstructionIso`
packages the resulting natural isomorphism from the descended canonical datum
to `F`; its object components are identities.
`descentPieceReconstructionIso` records the converse, already proved by
`pieceRestrictionIso`: reconstructing arbitrary descent data and restricting
again recovers each supplied piece functor through its explicit object
coordinates.

Together with `ambientNatTrans` and the uniqueness target, this supplies the
functor and natural-transformation reconstruction ingredients. This file does
not yet package them as an equivalence of functor categories or assert the
categorical pushout universal property.
