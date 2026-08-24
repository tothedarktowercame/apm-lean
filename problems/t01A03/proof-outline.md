# Proof Outline: t01A03

The statement represents the three pictured inclusions concretely and exposes
the relevant induced maps.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t01A03.md`

## Formal progress

- `apm_t01a03_fundamentalGroupMap_injective_of_retraction` proves the general
  split-monomorphism obstruction on fundamental groups. It closes the wedge
  branch using the frozen noninjectivity hypothesis.
- `apm_t01a03_noRetraction_twoCircles` proves that a connected space cannot
  retract onto two disjoint nonempty circles. It closes the third branch.
- `apm_t01a03_H1map_injective_of_retraction` proves functorially that a
  retraction makes the induced singular-`H₁` map injective.
- `apm_t01a03_noRetraction_of_H1map_zero` packages the resulting obstruction
  for any domain whose first homology contains a nonzero element.
- `apm_t01a03_noRetraction_circle_of_H1_nontrivial` specializes the entire
  middle-circle argument to the exact missing `Nontrivial H₁(Circle)` instance.
- `ConstructionTargets.SingularHomologyConcrete.circleHomeomorphSphereOne`
  identifies Mathlib's complex unit circle with the Euclidean one-sphere.
  The induced singular-homology isomorphism
  `circleSingularH1IsoInt` sends the named class
  `circleSingularH1Generator` to `1 : ℤ`, proving it nonzero and supplying
  the `Nontrivial` instance consumed by the middle-circle branch.

## Completion

All three retraction branches compile. The frozen theorem is unchanged and
has no remaining proof obligation.
