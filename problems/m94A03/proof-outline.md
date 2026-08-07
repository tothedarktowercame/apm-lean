# Proof Outline: m94A03

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A03.md`

## Compiled progress

- `apm_m94a03_logNormGradient` defines the classical candidate gradient.
- `apm_m94a03_norm_logNormGradient` proves its norm equals `‖x‖⁻¹` away
  from the origin.

## Remaining boundary

- establish radial `L²` integrability of `log ‖x‖` and the candidate gradient
  in dimensions three and four;
- prove the weak-gradient identity using punctured balls and a vanishing inner
  boundary term;
- in dimension two, prove uniqueness of weak gradients away from zero and use
  the nonintegrability of `‖x‖⁻¹` to rule out an `L²` weak gradient.
