# Proof Outline: t97J06

The coordinate formula and determinant integral are formalized and compile.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t97J06.md`

## Compiled steps

- `t97J06Map_on_cover` evaluates the concrete map on exponential coordinates.
- `t97J06_determinant_integral_zero` expands the two-by-two determinant and
  evaluates the inner cosine integral by the fundamental theorem of calculus
  and two-periodicity.
- `t97J06_circle_identity_homotopic_of_map_homotopic_const` restricts any
  proposed null-homotopy to the meridian `z ↦ (z,1)` and projects to the second
  coordinate, producing a null-homotopy of `id : Circle → Circle`.
- `t97J06_contractibleCircle_of_map_homotopic_const` packages that homotopy as
  an actual `ContractibleSpace Circle` instance using Mathlib's exact
  characterization of contractibility.
- `t97J06_not_homotopic_const_of_not_contractibleCircle` proves the complete
  final conjunct from the single missing input `¬ ContractibleSpace Circle`.

## Remaining boundary

It remains to prove `¬ ContractibleSpace Circle`. This is the standard
noncontractibility of the circle, obtainable
from winding number, `π₁(S¹) ≃ ℤ`, or `H₁(S¹;ℤ) ≃ ℤ`; none of those computations
is packaged in this Mathlib snapshot or in the proved repository corpus.
