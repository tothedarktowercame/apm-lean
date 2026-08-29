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

The remaining pseudococone-level construction is not a definitional
reindexing. For an actual glue isomorphism it must whisker these equations by
the piece functors and insert `pieceEquivalence.unitIso.symm` to cancel
`piece.functor ⋙ piece.inverse`. The two resulting comparison isomorphisms
must then be composed on either side of the whiskered actual glue. This exact
unit/counit coherence is the next seam; no pseudococone equivalence or based
group pushout is claimed here.
