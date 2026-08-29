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

The reverse functor still requires a cover-dependent choice of common object
coordinate for each ambient point and a proof that glue naturality recovers
`TwoOpenDescentDatum.overlap_eq`; that work is not assumed here. Consequently
this file does not yet claim an equivalence with all pseudococones, a
`Limits.IsColimit`, or an ordinary `Limits.Pushout`.
