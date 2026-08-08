# Proof Outline: m96J03

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96J03.md`

## Compiled progress

- `apm_m96j03_integral_ballIndicator` reduces the volume term to the closed
  unit ball.
- `apm_m96j03_zero_dim` proves the complete dimension-zero flux identity by
  reducing the Laplacian to an empty sum and the sphere to the empty set.
- `apm_m96j03_measurable_ballIndicator` proves measurability of the frozen
  ball indicator via the closed-ball indicator representation.
- `apm_m96j03_laplacian_const` verifies the coordinate Laplacian on constants.
- `apm_m96j03_coordinate_second_derivative` transports each frozen scalar
  coordinate term to the matching diagonal evaluation of Mathlib's second
  iterated Fréchet derivative.

## Remaining boundary

- for positive dimension, prove the ball-specialized Gauss–Green identity;
- sum the now-transported coordinate identities against the precise standard
  orthonormal-basis indexing used by Mathlib's intrinsic Laplacian;
- alternatively develop spherical averaging and differentiate under the
  sphere integral;
- identify Mathlib's `volume.toSphere` normalization with the frozen
  `(n-1)`-dimensional Hausdorff measure restricted to the unit sphere.

Closer hop 3 leaves an honest partial: the coordinate calculus bridge now
compiles, while the geometric Gauss–Green and surface-measure identification
remain unavailable.
