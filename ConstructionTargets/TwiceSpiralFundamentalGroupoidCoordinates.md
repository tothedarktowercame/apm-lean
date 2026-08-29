# Twice-spiral fundamental-groupoid coordinates

This target defines the exact coordinate span

```text
FundamentalGroupoid BoundaryTorus
  ⇉ FundamentalGroupoid SolidTorus
```

whose legs are `boundaryInclusion` and `boundaryInclusion ∘ h`. A
`CoordinatePseudoCocone` is a pair of solid-torus functors equipped with an
invertible overlap comparison; its morphisms satisfy the corresponding glue
square. Thus the construction retains the bicategorical coherence rather than
replacing it by equality.

`actual_left_leg_in_coordinates` and `actual_right_leg_in_coordinates` record
the exact orientation already proved by the collar deformation equivalences:
inverse overlap equivalence, actual inclusion, then forward piece equivalence.

The remaining mapping-category transport is not definitional. It must whisker
actual pseudococones through the three equivalences and insert their unit and
counit natural isomorphisms to compare the displayed composites with the
coordinate legs. The two strict coordinate equations in this file provide the
central arrows for that construction.

`BasedTwiceSpiralCoordinateInterface d` states the smallest subsequent based
layer. It retains explicit basepoint equalities and asks that the induced
automorphism-group maps become the two homomorphisms used by
`TwiceSpiralFundamentalGroupPushout`. Once supplied from the banked π₁
coordinates, the groupoid pseudopushout can be specialized to the based group
pushout and then to `ZMod 2`; this target does not assume that passage.
