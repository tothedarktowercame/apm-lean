# Proof Outline: t02A05

The Lean statement encodes the ambient differential form, tangent projection,
outward coefficient, and Hausdorff-measure sphere integral concretely.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-t02A05.md`

## Formal progress

- `apm_t02a05_quadratic_minimum` proves that the expected explicit flux
  formula has minimum `44π/15`, attained exactly when the first two center
  coordinates are `1` and `2`.

## Remaining boundary

It remains to prove the explicit flux formula. The intended Stokes argument
reduces the surface integral to a translated unit-ball integral and standard
second moments. Mathlib does not currently connect exterior derivatives to
the file's custom tangent-projection/Hausdorff-measure surface integral.
Direct calculation would require orthogonal-projection coordinate algebra,
surface-measure translation, and sphere moments. The nearby `t92J09` and
`t01J06` artifacts are blocked at the same interface.
