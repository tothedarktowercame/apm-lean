# Two-open descent object reconstruction

`canonicalTwoOpenDescentDatum F` restricts an ambient functor `F` along the
two subtype inclusions. Its common object coordinate is literally
`F.obj ⟨x⟩`. The overlap equation is proved from
`map_pathInPiece_coverPieceInclusion`: mapping either subtype lift of an
overlap path back into the ambient space gives the original path class.

`canonicalReconstructionAppIso` records that reconstruction has exactly the
same object as `F`; its component is the identity isomorphism.
`descentPieceReconstructionIso` records the converse, already proved by
`pieceRestrictionIso`: reconstructing arbitrary descent data and restricting
again recovers each supplied piece functor through its explicit object
coordinates.

The remaining reconstruction theorem is naturality of the identity object
components. Equivalently, evaluation of a subordinate subdivision for the
canonical datum must equal `F.map` of the original path class. This requires a
finite functorial telescoping theorem for `composeFin`, including the endpoint
casts from `PathTwoOpenSubdivision.concat_piece_homotopic`. No natural
isomorphism or categorical pushout is asserted until that morphism theorem is
proved.
