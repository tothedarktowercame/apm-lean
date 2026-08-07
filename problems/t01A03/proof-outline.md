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

## Remaining boundary

For the separating middle circle, functoriality would make its induced `H₁`
map injective, contradicting the frozen assertion that the map is zero once
one knows integral `H₁(Circle)` is nonzero. The current Mathlib singular
homology API provides the functor and homotopy invariance, but the searches in
this hop found no compiled circle-homology computation.
