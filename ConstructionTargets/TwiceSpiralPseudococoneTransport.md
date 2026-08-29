# Twice-spiral pseudococone transport

The collar deformation equivalences induce three honest equivalences of
functor categories via Mathlib's `Equivalence.congrLeft`:

- functors on the left collar piece versus functors on `SolidTorus`;
- functors on the right collar piece versus functors on `SolidTorus`;
- functors on the collar intersection versus functors on `BoundaryTorus`.

The public object formulas show that each forward transport is literal
precomposition with the inverse fundamental-groupoid equivalence.
`left_span_coordinate_equation` and `right_span_coordinate_equation` retain
the already-proved orientation

```text
overlap.inverse ⋙ actual inclusion ⋙ piece.functor = coordinate leg.
```

`leftSpanComparison` and `rightSpanComparison` implement that non-definitional
reindexing. Each first whisks the strict span-coordinate equation and then
uses `pieceEquivalence.unitIso.symm` to cancel
`piece.functor ⋙ piece.inverse`.

`transportedOverlapGlue` whisks the actual collar glue through the inverse
overlap equivalence. `actualPseudoCoconeToCoordinateObj` brackets it by the
two span comparisons. The comparison naturality lemmas and
`three_square_pasting` prove the glue square for transported morphisms, giving
the compiled `actualPseudoCoconeToCoordinateFunctor`.

`reverseLeftSpanComparison` and `reverseRightSpanComparison` implement the
opposite span comparison. They precompose the strict coordinate equations by
the forward overlap equivalence and use its `funInvIdAssoc`; thus the overlap
unit is retained explicitly. `reverseTransportedOverlapGlue` then whisks the
coordinate glue through that forward equivalence.

Their naturality squares, including the inverse left comparison, are pasted
by the same typed three-square lemma to give
`coordinateToActualPseudoCoconeMap` and the compiled reverse functor
`coordinateToActualPseudoCoconeFunctor`.

The remaining categorical seam is the objectwise unit/counit between the two
pseudococone functors. Its piece components are the unit/counit of the left
and right `congrLeft` equivalences, but its overlap proof must compare those
components with both nested span-comparison composites and the overlap
equivalence triangle identities. Until that proof is compiled, no category
equivalence or composite gluing-to-coordinate equivalence is claimed. No
based group pushout is claimed here.
