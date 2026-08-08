# Proof Outline: m97A03

The frozen Lean theorem is present in `lean/Main.lean`. Two quantitative
ingredients are compiled:

- `t * sqrt (t + 3) ≤ 2` on `[0,1]`;
- `∫_[0,1] s ^ (-1/2) = 2`.
- away from the null endpoint,
  `sqrt ((t+3)/s) = sqrt (t+3) * s^(-1/2)`;
- the nonlinear integrand difference is pointwise bounded by
  `2 * s^(-1/2) * |u-v|` using `Real.abs_sin_sub_sin_le`.
- the singular majorant is integrable on the closed interval;
- integrating under a uniform bound `|u s-v s| ≤ B` gives `≤ 4*B`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m97A03.md`

## Remaining boundary

- establish dominated continuity in the parameter `t` despite the endpoint
  singularity. Hop 4 identifies
  `intervalIntegral.continuousWithinAt_of_dominated_interval` as the engine;
  the remaining assembly is the exact statement
  `ContinuousOn (fun t ↦ ∫ s in Icc 0 1,
  sqrt ((t+3)/s) * sin (t*u s)) (Icc 0 1)` for every `u` continuous there;
- package the integral operator on `ContinuousMap (Icc 0 1) ℝ`;
- instantiate the compiled uniform-bound estimate with the `ContinuousMap`
  sup norm and the factor `|lam|`;
- apply the contraction theorem and extend the fixed point to `ℝ → ℝ`.

The two proved estimates account exactly for the threshold `|lam| < 1/4`.
