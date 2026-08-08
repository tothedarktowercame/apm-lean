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

## Remaining boundary

For the separating middle circle, the functorial injectivity and zero-map
contradiction are now compiled. The only remaining input is a nonzero element
of integral `H₁(Circle)`. The current Mathlib singular
homology API provides the functor and homotopy invariance, but the searches in
this hop found no compiled circle-homology computation.
