# Proof Outline: m95J04

The frozen theorem has a compiling partial Lean development.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m95J04.md`

## Compiled progress

- The Green kernel is nonnegative and at most `1/4` on the unit square.
- The specific nonlinearity is globally continuous.
- Its exact reflection identity under `t ↦ 1-t` is proved.
- `apm_m95J04_specific_eq_cos` gives its product-to-sum representation, and
  `apm_m95J04_specific_lipschitz` proves the sharp global Lipschitz-one bound.
- `apm_m95J04_green_reflection` proves simultaneous reflection invariance of
  the Green kernel.

## Remaining boundary

- bundle the Green integral as an operator on `ContinuousMap (Icc 0 1) ℝ`;
- prove its fixed points correspond to the frozen within-derivative solution
  predicate, including endpoint regularity;
- lift the kernel and nonlinear Lipschitz estimates to the sup norm and apply
  Banach's fixed-point theorem;
- derive reflection symmetry from uniqueness.
