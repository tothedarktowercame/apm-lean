# Proof Outline: a98A07

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a98A07.md`

## Compiled progress

- `apm_a98A07_log_ratio_neg` proves the logarithmic factor never vanishes on
  `(0,2π)`; only the integrable singularity at zero remains.
- `apm_a98A07_majorant` names the frozen boundary bound;
  `apm_a98A07_majorant_measurable` and `apm_a98A07_majorant_pos` establish its
  global measurability and strict positivity on `(0,2π)`.
- `apm_a98A07_differentiableOn_of_locallyUniform` applies Mathlib's packaged
  Weierstrass theorem, closing holomorphicity of the eventual locally uniform
  limit.

## Remaining bridges

1. Prove the exact Lean statement
   `Integrable apm_a98A07_majorant
   ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi)))` by logarithmic
   substitution.  The general Jacobian and improper-integral substitution
   theorems were checked, but each leaves this transformed integrability
   obligation rather than proving it.
2. Select the measurable a.e. boundary limit and apply dominated convergence
   in L¹, producing a measurable `h` and convergence of
   `∫ t, ‖F n t - h t‖` to zero for the restricted measure.
3. Use Cauchy's formula and a compact-subdisk kernel bound to obtain locally
   uniform convergence from that boundary L¹ convergence.

The former fourth bridge is closed by
`TendstoLocallyUniformlyOn.differentiableOn` from
`Analysis.Complex.LocallyUniformLimit`.
