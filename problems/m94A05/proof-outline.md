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
- `apm_m94a05_extend` uses `Set.projIcc` to continuously extend interval maps
  while retaining their sup-norm bound.
- `apm_m94a05_picardMap` bundles the operator on
  `ContinuousMap (Icc 0 Real.pi) ℝ`.
- `apm_m94a05_norm_picardMap_le` proves `‖T u‖ ≤ ε + π ‖u‖²`.

## Remaining boundary

- prove the bundled sup-norm difference estimate, then establish invariance
  and strict contractivity on the closed radius-`2ε` ball;
- apply Banach's fixed-point theorem and transport the result to the frozen
  unrestricted-function conclusion.
