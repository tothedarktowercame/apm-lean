# Proof Outline: t02A05

The Lean statement encodes the ambient differential form, tangent projection,
outward coefficient, and Hausdorff-measure sphere integral concretely.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A05.md`

## Formal progress

- `apm_t02a05_quadratic_minimum` proves that the expected explicit flux
  formula has minimum `44π/15`, attained exactly when the first two center
  coordinates are `1` and `2`.
- `apm_t02a05_volume_unit_ball`, reused from closed artifact `t92J09`, proves
  that the unit three-ball has volume `4π/3`.

## Remaining boundary

It remains to prove the explicit flux formula. The intended Stokes argument
reduces the surface integral to a translated unit-ball integral and standard
second moments. Mathlib does not currently connect exterior derivatives to
the file's custom tangent-projection/Hausdorff-measure surface integral.
Direct calculation would require orthogonal-projection coordinate algebra,
surface-measure translation, and the coordinate second moment
`∫ x₀² = 4π/15`. Mathlib's polar `Measure.toSphere` is not definitionally the
Hausdorff subtype measure used by the frozen statement.
