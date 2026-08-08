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
- `apm_m95J02_radialProfile` and
  `apm_m95J02_fundamental_eq_radialProfile` factor the Euclidean kernel through
  its scalar radius.
- `apm_m95J02_hasDerivAt_radialProfile_of_two_lt` proves the exact derivative
  of the higher-dimensional power-law profile at every nonzero radius.

## Remaining boundary

- derive the Laplacian of `z ↦ v ‖z‖` from Mathlib's orthonormal-basis formula;
- prove the punctured-ball integration-by-parts identity and its boundary
  limit at the origin;
- justify differentiating the singular convolution and transport the weak
  fundamental-solution identity to the pointwise Poisson equation.

Closer hop 3 leaves this theorem honest and partial: the scalar derivative is
compiled, but the radial Laplacian chain rule and the two distributional PDE
bridges are not packaged in Mathlib and were not completed locally.
