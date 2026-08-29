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

The four declarations `actualLeftRoundTripIso`,
`actualRightRoundTripIso`, `coordinateLeftRoundTripIso`, and
`coordinateRightRoundTripIso` now expose those piece components. Their four
naturality theorems give the complete piecewise natural comparison for both
round trips without replacing a unit or counit by an identity.

The remaining categorical seam is specifically the overlap component.
Expanding the actual-side glue square produces the overlap equivalence unit
and inverse unit, the two piece units, mapped `eqToHom` transports from the
two span-coordinate equations, and the original glue naturality component.
A dedicated triangle/pasting normalization for that exact composite is still
required before the piecewise units can be packaged as pseudococone
isomorphisms. Until then, no category equivalence, composite
gluing-to-coordinate equivalence, or based group pushout is claimed.

`actualGlue_overlapUnit_naturality` now isolates the central part of that
normalization. It specializes `P.glue.hom.naturality` to the overlap
equivalence's unit component and explicitly retains the induced maps through
`intersectionToLeftOpen` and `intersectionToRightOpen`.
The component lemmas `actualLeftRoundTrip_unit_cancel_app` and
`actualRightRoundTrip_unit_cancel_app` separately discharge the literal
piece-unit hom/inverse pairs at the two actual overlap images; they do not
identify any overlap and piece objects.

`EquivalenceSpanRoundTrip.spanRoundTrip_triangle` now proves the formerly
missing span triangle generically from equivalence coherence.  The concrete
theorems `actualLeft_span_roundTrip_triangle` and
`actualRight_span_roundTrip_triangle` specialize it to both collar legs while
retaining the overlap `funInvIdAssoc`, the proof-carrying span equality, and
the inverse piece-unit component.  The outgoing orientation needed on the
right is exported as `actualRight_span_roundTrip_triangle_inv`.

`actualRoundTrip_glue_square` performs the typed three-part paste of those
triangles with `actualGlue_overlapUnit_naturality`. `actualRoundTripHom` uses
that square directly, while `actualRoundTripInv` derives the inverse square
by cancelling the two whiskered piece isomorphisms. They form the objectwise
`actualRoundTripIso`; the existing piece-unit naturality equations package
these as `actualRoundTripNatIso`, oriented from the identity functor to
forward coordinate transport followed by reverse transport.

The coordinate-side coherence packet now exports
`coordinateLeft_span_roundTrip_counit_triangle`,
`coordinateRight_span_roundTrip_counit_triangle_inv`, and
`coordinateGlue_overlapCounit_naturality`.  Thus both concrete span
specializations and the central glue square are available with the overlap
equivalence counit retained explicitly.
`coordinateRight_span_roundTrip_counit_cancel` postcomposes the inverse
right triangle with the whiskered right counit and cancels the inverse/hom
pair.  It is the complete outgoing-right block required by the coordinate
glue square.
`coordinateMiddle_counit_conjugation` now packages the central block in the
exact natural-transformation type used by that paste: inverse-overlap
whiskering of the coordinate glue equals the glue conjugated by the left
counit comparison and inverse right counit comparison.

`whiskerLeft_three_comp` proves the generic three-arrow whiskering formula,
and `coordinateRoundTrip_whiskered_reverseGlue` now exposes that previously
parenthesized reverse glue as its three separately whiskered arrows without
unfolding either span comparison.

`three_prefix_four_terminal_substitution`,
`four_context_middle_substitution`, and
`right_nested_prefix_terminal_substitution` encode exactly the associations
produced by that expansion.  They allow `coordinateRoundTrip_glue_square` to
paste the incoming triangle, middle conjugation, and outgoing cancellation
without unfolding the comparisons.

The resulting `coordinateRoundTripHom`, inverse, objectwise isomorphism, and
`coordinateRoundTripNatIso` give the coordinate-side counit.  Together with
`actualRoundTripNatIso`, they define
`actualCoordinatePseudoCoconeEquivalence`; its triangle identity reduces
piecewise to the two underlying functor-category equivalence triangles.
Finally, `gluingFundamentalGroupoidCoordinateEquivalence` composes this with
the collared two-open pseudopushout mapping equivalence.  This remains a
pseudococone mapping-category result: no ordinary categorical pushout or
based fundamental-group pushout is asserted.
