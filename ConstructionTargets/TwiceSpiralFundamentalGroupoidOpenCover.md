# Twice-spiral fundamental-groupoid open cover

`SolidTorusGluingOpenCover` already constructs the required collar geometry
on the actual quotient `Gluing h`. Its `leftOpen h` and `rightOpen h` are open,
cover the quotient, and deformation retract to the two copies of
`SolidTorus`; their intersection deformation retracts to `BoundaryTorus`.

This target packages that geometry for fundamental groupoids:

- `gluingFundamentalGroupoidPseudopushoutEquivalence` directly specializes
  the generic two-open pseudopushout mapping-category equivalence;
- `gluingPseudopushoutPostcomposeNatIso` specializes its reviewed target-
  postcomposition natural isomorphism to the same collared cover;
- `leftFundamentalGroupoidEquivalence` and
  `rightFundamentalGroupoidEquivalence` identify the piece groupoids with the
  solid-torus groupoid;
- `overlapFundamentalGroupoidEquivalence` identifies the overlap groupoid
  with the boundary-torus groupoid;
- `overlapToLeft_groupoid_coordinate` and
  `overlapToRight_groupoid_coordinate` transport the actual subtype
  inclusions to `boundaryInclusion` and `boundaryInclusion ∘ h`, respectively.

The next seam is algebraic/categorical rather than missing collar topology:
transport the pseudococone category across these three groupoid equivalences
and identify its based automorphism-group pushout with
`TwiceSpiralPushout d`. That step must retain the two inclusion functors and
basepoint-change data; this file makes no fundamental-group presentation or
pushout-group claim.
