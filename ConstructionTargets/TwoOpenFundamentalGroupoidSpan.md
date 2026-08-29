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
`obj_eq` coordinates. The remaining comparison with `DescentObject` is the
naturality proof for these components, obtained by translating a path in the
nested overlap subtype and applying `D.overlap_eq`. Until that theorem and the
category of pseudococone morphisms are compiled, no `Limits.IsColimit` or
ordinary `Limits.Pushout` claim is made.
