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

`descentReconstructionHom` and `descentReconstructionInv` use respectively
the inverse and forward transformations of `pieceRestrictionIso`. Their
overlap compatibility is proved after transporting both sides to the common
`D.obj` coordinate. `descentReconstructionAppIso` proves the two composites
are identities using `CompatibleNatTrans.ext`, and
`descentReconstructionIso` proves naturality from
`ambientNatTrans_restriction_app`.

`twoOpenDescentEquivalence` packages the resulting equivalence between
ambient fundamental-groupoid functors and compatible two-open descent data.
This is an equivalence of functor/descent-data categories; no
`CategoryTheory.Limits.Pushout` object or pushout claim is made here.
