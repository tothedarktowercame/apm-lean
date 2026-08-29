# Category of two-open descent data

`DescentObject` wraps `TwoOpenDescentDatum`; its morphisms are the minimal
`CompatibleNatTrans` records. `compatibleId` and `compatibleComp` give the
category structure. Composition preserves overlap compatibility through the
explicit common-coordinate conjugation formula
`transportedPieceApp_comp`.

`restrictionFunctor` restricts ambient fundamental-groupoid functors and
whiskers ambient natural transformations along the two cover inclusions.
`reconstructionFunctor` uses `twoOpenDescentFunctor` on objects and
`ambientNatTrans` on morphisms.

`reconstructionRestrictionIso` is the natural isomorphism from reconstructing
a canonical restriction back to the original ambient functor, using the
banked `canonicalReconstructionIso`.

The opposite natural isomorphism in the descent category remains to be
packaged. Its two piece components are the inverses of `pieceRestrictionIso`;
the next theorem must prove their common-coordinate overlap compatibility and
the naturality of that counit with respect to `CompatibleNatTrans`. Therefore
this target does not yet claim an equivalence of categories or a categorical
pushout.
