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

The remaining categorical seam is the reverse transport functor and its
unit/counit isomorphisms. Those must use the opposite equivalence coherences;
they cannot treat the three equivalences as identities. Only after that
equivalence is combined with the gluing pseudopushout may one begin the
explicit based automorphism-group comparison. No based group pushout is
claimed here.
