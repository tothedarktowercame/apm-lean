# Proof Outline: m95J02

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J02.md`

## Compiled progress

- `apm_m95J02_sphereArea_two` verifies the Gamma-function normalization
  `ω₂ = 2π`.
- `apm_m95J02_fundamental_two` unfolds the exact logarithmic kernel in
  dimension two.
- `apm_m95J02_sphereArea_pos` proves the Gamma normalization positive in all
  positive dimensions.
- `apm_m95J02_power_denominator_pos` and
  `apm_m95J02_fundamental_neg` compile the denominator and sign calculations
  for every `n > 2`.

## Remaining boundary

- derive the Laplacian of `z ↦ v ‖z‖` from Mathlib's orthonormal-basis formula;
- prove the punctured-ball integration-by-parts identity and its boundary
  limit at the origin;
- justify differentiating the singular convolution and transport the weak
  fundamental-solution identity to the pointwise Poisson equation.
