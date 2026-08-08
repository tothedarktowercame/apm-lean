# Proof Outline: m97A03

The frozen Lean theorem is present in `lean/Main.lean`. Two quantitative
ingredients are compiled:

- `t * sqrt (t + 3) ≤ 2` on `[0,1]`;
- `∫_[0,1] s ^ (-1/2) = 2`.
- away from the null endpoint,
  `sqrt ((t+3)/s) = sqrt (t+3) * s^(-1/2)`;
- the nonlinear integrand difference is pointwise bounded by
  `2 * s^(-1/2) * |u-v|` using `Real.abs_sin_sub_sin_le`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m97A03.md`

## Remaining boundary

- establish dominated continuity in the parameter `t` despite the endpoint
  singularity;
- package the integral operator on `ContinuousMap (Icc 0 1) ℝ`;
- integrate the compiled pointwise domination and replace `|u s-v s|` by the
  `ContinuousMap` sup norm to derive the constant `4 * |lam|`;
- apply the contraction theorem and extend the fixed point to `ℝ → ℝ`.

The two proved estimates account exactly for the threshold `|lam| < 1/4`.
