# Proof Outline: m94A03

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A03.md`

## Compiled progress

- `apm_m94a03_logNormGradient` defines the classical candidate gradient.
- `apm_m94a03_norm_logNormGradient` proves its norm equals `‖x‖⁻¹` away
  from the origin.
- The norm identity now holds globally, including the totalized origin.
- The logarithm and vector gradient are strongly measurable for arbitrary
  measures.
- `apm_m94a03_logNormGradient_memLp_iff` reduces all vector `Lᵖ` questions
  exactly to the scalar radial function `x ↦ ‖x‖⁻¹`.
- `apm_m94a03_invNorm_memLp_two_ball_fin_three` proves inverse-radius `L²`
  membership on the three-dimensional unit ball using the reusable radial
  integration module.
- `apm_m94a03_logNormGradient_memLp_two_ball_fin_three` transfers this to the
  vector classical-gradient candidate.

## Remaining boundary

- establish scalar radial `L²` integrability of `log ‖x‖` in dimension three,
  and of both scalar functions in dimension four;
- prove the weak-gradient identity using punctured balls and a vanishing inner
  boundary term;
- in dimension two, prove uniqueness of weak gradients away from zero and use
  the nonintegrability of `‖x‖⁻¹` to rule out an `L²` weak gradient.
