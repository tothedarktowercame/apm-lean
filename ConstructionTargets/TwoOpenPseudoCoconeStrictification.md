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

After mapping `overlapPath_map_eq_pathInPiece` through both piece functors and
expanding these endpoint isomorphisms, the remaining goal contains three pairs
of independently generated `eqToHom`s around `P.glue.hom.naturality`. A typed
multi-transport cancellation theorem aligning those pairs is still required
before `strictifiedDescentDatum` can be packaged. That equation is not assumed
here. No equivalence or ordinary pushout is claimed.
