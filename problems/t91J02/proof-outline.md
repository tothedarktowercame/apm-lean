# Proof Outline: t91J02

The Lean artifact now isolates the elementary half of the standard
fundamental-group obstruction.  The maps
`apm_t91J02_circleInclusion : C(Circle, Circle × Circle)` and
`apm_t91J02_circleProjection : C(Circle × Circle, Circle)` are defined, and
their composite is proved to be the identity.  Hence `Circle` is a retract of
the concrete torus.

`apm_t91J02_circleRetract_of_homeomorph` transports this retraction across any
hypothetical torus--sphere homeomorphism, and
`apm_t91J02_not_homeomorph_of_no_circle_retract` reduces the frozen conclusion
exactly to the absence of such a sphere retraction.

`apm_t91J02_fundamentalGroupMap_injective_of_retract` and
`apm_t91J02_no_circle_retract_of_fundamentalGroup` compile the complete
functorial contradiction from a nontrivial circle fundamental group and
subsingleton sphere fundamental groups.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t91J02.md`

## Remaining bridge

A homeomorphism from the torus to the concrete metric two-sphere would
transport this retraction to a circle retraction of that sphere. It remains
to supply the concrete fundamental-group instances consumed by the compiled
no-retraction lemma. Standard routes use either:

- fundamental groups: a retraction makes `π₁(Circle)` a retract of `π₁(S²)`,
  but these groups are `ℤ` and trivial; or
- first singular homology: a retraction splits the induced map on `H₁`, while
  `H₁(Circle) = ℤ` and `H₁(S²) = 0`.

This Mathlib snapshot has the relevant functorial frameworks but does not
package the required computations for `Circle` and the displayed metric
sphere.  Nearby partial artifacts record the same missing bridge.
