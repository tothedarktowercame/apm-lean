# Proof Outline: m96J03

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J03.md`

## Compiled progress

- `apm_m96j03_integral_ballIndicator` reduces the volume term to the closed
  unit ball.
- `apm_m96j03_zero_dim` proves the complete dimension-zero flux identity by
  reducing the Laplacian to an empty sum and the sphere to the empty set.

## Remaining boundary

- for positive dimension, prove the ball-specialized Gauss–Green identity;
- alternatively develop spherical averaging and differentiate under the
  sphere integral;
- identify Mathlib's `volume.toSphere` normalization with the frozen
  `(n-1)`-dimensional Hausdorff measure restricted to the unit sphere.
