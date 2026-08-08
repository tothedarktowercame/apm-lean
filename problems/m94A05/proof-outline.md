# Proof Outline: m94A05

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A05.md`

## Compiled progress

- `apm_m94a05_picard` defines the raw nonlinear integral operator.
- `apm_m94a05_picard_integrable` proves each integral section is interval
  integrable for a continuous input.
- `apm_m94a05_kernel_square_le` proves the pointwise radius-square estimate.
- `apm_m94a05_kernel_square_sub_le` proves the pointwise Lipschitz estimate
  with factor `2 * R` on a radius-`R` ball.
- `apm_m94a05_picard_continuous` applies dominated convergence with the
  integrable majorant `u^2` and proves global continuity in the free parameter.

## Remaining boundary

- bundle the now-proved-continuous operator on
  `ContinuousMap (Icc 0 Real.pi) ℝ`;
- lift the pointwise bounds to the sup norm, establish invariance and strict
  contractivity on the closed radius-`2ε` ball;
- apply Banach's fixed-point theorem and transport the result to the frozen
  unrestricted-function conclusion.
