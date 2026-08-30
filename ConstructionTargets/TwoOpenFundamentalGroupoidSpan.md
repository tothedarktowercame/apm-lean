# Two-open fundamental-groupoid span

`CoverOverlap` is the subtype carrying membership in both opens.
`overlapToPiece` gives its inclusions into the `U` and `V` cover pieces, and
`overlapFundamentalGroupoidMap` applies the fundamental-groupoid functor.

The two composites through the piece inclusions agree propositionally as
functors to `FundamentalGroupoid X`; `ambientSpanCocone` packages this strict
ambient cocone.

For functors into an arbitrary category, `StrictFunctorCocone` records the
ordinary 1-categorical condition: the two restricted functors must be equal.
That is not the interface carried by `TwoOpenDescentDatum`, whose piece-object
coordinates are only propositionally identified with a common chosen object.
`PseudoFunctorCocone` therefore records the correct condition: a specified
natural isomorphism between the overlap restrictions.

`descentOverlapAppIso` constructs the required object component from the two
`obj_eq` coordinates. `descentOverlapAppIso_naturality` proves its naturality
by eliminating an overlap fundamental-groupoid morphism to a nested-subtype
path, forgetting to the ambient path, and applying `D.overlap_eq`.
`descentOverlapIso` and `descentPseudoCocone` package the resulting natural
isomorphism and pseudococone.

`PseudoFunctorCoconeHom` is the honest category of pairs of piece natural
transformations whose square commutes with the specified glue isomorphisms.
Identity and composition retain that square. `descentPseudoCoconeMap` converts
the common-coordinate condition of `CompatibleNatTrans` into precisely this
square, and `descentToPseudoCoconeFunctor` packages the construction.

`postcomposePseudoFunctorCoconeObj` postcomposes both legs with a target
functor and transports the glue by `Functor.isoWhiskerRight`.
`postcomposePseudoFunctorCoconeMap` uses `Functor.whiskerRight` on both
components; its glue square is the image under the target functor of the
original componentwise square. These operations assemble into
`postcomposePseudoFunctorCoconeFunctor`. The accompanying left/right object
and map formulas are definitional equalities exposed as simp lemmas.

For the reverse direction, `strictifiedObject` chooses the left piece object
when the point lies in `U` and otherwise the right piece object, using the
cover hypothesis. `strictifiedObjectIso` compares each original piece object
with that common coordinate; on the right side of the overlap it uses the
inverse glue component. `strictifiedPieceFunctor` conjugates every map through
these isomorphisms and proves both functor laws, while
`pieceStrictificationIso` exposes the comparison natural isomorphism.

The remaining theorem must transport `P.glue.hom.naturality` from its nested
overlap objects through the endpoint `eqToHom`s introduced by both
`strictifiedObjectIso` components. Once that equation is compiled it supplies
`TwoOpenDescentDatum.overlap_eq`; it is not assumed here. Consequently this
file does not yet claim an equivalence with all pseudococones, a
`Limits.IsColimit`, or an ordinary `Limits.Pushout`.
