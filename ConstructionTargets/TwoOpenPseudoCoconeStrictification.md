# Strictification required for reverse two-open descent

An arbitrary `PseudoFunctorCocone` cannot be converted directly to a
`DescentObject`. Its glue identifies the two overlap objects by an isomorphism,
while `TwoOpenDescentDatum.obj_eq` asks for literal equalities with one common
object. Lean has no principle turning arbitrary categorical isomorphisms into
equalities of objects.

`CoordinatedPseudoFunctorCocone` records the precise strictification data:

- a common object function on the ambient space;
- equality coordinates for both piece functors;
- agreement of those coordinates with the pseudococone glue;
- the overlap morphism equation in common coordinates.

`CoordinatedPseudoFunctorCocone.toDescentObject` is the honest reverse
construction under those hypotheses. `HasStrictCommonObjectCoordinates`
isolates the first unavoidable condition missing from a general pseudococone.

`TwoOpenFundamentalGroupoidSpan` now provides that separate construction as
`strictifiedObject`, `strictifiedPieceFunctor`, and
`pieceStrictificationIso`. This file additionally banks
`iso_naturality_conjugation`, the categorical core which turns the glue
naturality square into equality of conjugated piece arrows.

`overlapPath_map_eq_pathInPiece` now supplies the proof-carrying comparison
between the nested overlap path and each independently constructed
`pathInPiece` representative. It uses explicit endpoint `eqToHom`s and
`FundamentalGroupoid.conj_eqToHom`; it does not identify subtype witnesses
definitionally.

`strictifiedObjectIso_overlap_hom` and `strictifiedObjectIso_overlap` now
normalize the strictification comparison at an arbitrary overlap endpoint.
They state, with explicit subtype-object transports, that the right comparison
is the inverse glue component followed by the left comparison. The iso-valued
form controls both the inverse at a path source and the hom at its target.
`functor_map_eqToHom` separately normalizes mapping one such transport.

`strictifiedOverlapIso` packages the exact natural overlap isomorphism between
the two strictified piece functors by whiskering `pieceStrictificationIso` on
both sides of `P.glue`. Thus glue naturality and all functorial endpoint
transport are now present in one compiled natural isomorphism.

`transported_glue_strictification_identity` performs the required cancellation
entirely inside the target category: canonical overlap objects, independently
constructed piece objects, and the common object remain distinct parameters,
and explicit equalities connect them. `strictifiedOverlapIso_hom_app`
specializes it to prove every component of `strictifiedOverlapIso.hom` is the
identity.

`strictifiedOverlapIso_map_eq` performs naturality normalization with explicit
left and right identity composition, avoiding conversion across the piece and
overlap source categories. `strictified_overlap_map_eq` then maps
`overlapPath_map_eq_pathInPiece` through each strictified functor. Because its
object map depends only on the ambient point, the resulting endpoint
transports are endomorphism `eqToHom`s and cancel before the two nested-overlap
maps are compared.

`strictifiedDescentDatum` and `strictifiedDescentObject` now package the full
reverse object construction. Their overlap equation is derived solely from
the supplied pseudococone glue; there is no independent overlap premise.
`strictifiedDescentPieceIso` exposes the original-to-strictified comparison on
each piece. `strictifiedPieceNatTrans` now conjugates both components of an
arbitrary `PseudoFunctorCoconeHom` through those comparisons, giving the
correct natural transformations between the strictified piece functors.

`six_arrow_iso_conjugation` performs the exact cancellation around a glue
naturality square, and `strictifiedPieceNatTrans_glue` applies it without
identifying any isomorphic objects definitionally.  Component normalization
through the identity strictified glue yields
`strictifiedPieceNatTrans_overlap_app`, hence
`strictifiedCompatibleNatTrans`.

`iso_conjugation_comp` proves that these conjugated transformations compose;
together with the identity calculation it packages
`pseudoCoconeToDescentFunctor`, the reverse functor on both objects and
morphisms. Its object and piece-map simp lemmas expose the construction.

`pseudoCoconeStrictificationHom` uses the two `pieceStrictificationIso.hom`
components and derives its glue square from
`strictifiedOverlapIso_hom_app`. `iso_square_inverse` derives the inverse glue
square algebraically, so `pseudoCoconeStrictificationInv` does not assume a
second compatibility condition. `pseudoCoconeStrictificationIso` proves both
inverse laws via `PseudoFunctorCoconeHom.ext`.

Finally, `pseudoCoconeStrictificationNatIso` packages these objectwise
isomorphisms naturally in the explicit orientation
`Functor.id _ ≅ pseudoCoconeToDescentFunctor hcover ⋙
descentToPseudoCoconeFunctor`. Naturality is the componentwise cancellation
of each source piece isomorphism against the conjugated map. The descent-side
natural isomorphism remains separate. No categorical equivalence or ordinary
pushout is claimed here.
