# Proof Outline: m99J03

The canonical Lean attempt is in `lean/Main.lean`. It currently has one
documented boundary covering parts (a) and (b); part (c) is fully compiled.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m99J03.md`

## Compiled progress

- `apm_m99j03_dilation_integrable` proves integrability of every dilated
  profile against a compactly supported continuous test function.
- `apm_m99j03_dilation_tendsto` proves part (c) by dominated convergence.
  Compact support supplies a closed ball containing the test function's
  support. Every `x / n` lies in that same ball (with `n = 0` handled
  separately), continuity bounds `ψ` there, and `C * ‖φ x‖` is an integrable
  majorant.
- `apm_m99j03_triangle_eq_scaled_profile` rewrites every positive-index
  triangle as the normalized dilation `n * triangle 1 (n*x)`.
- `apm_m99j03_triangle_one_eq_max` identifies the unit profile with
  `max (1-|x|) 0`; its continuity and compact support in `[-1,1]` are compiled.
- `apm_m99j03_integral_triangle_one` proves that the unit triangular profile
  has total mass one by reducing to `[-1,1]`, splitting at zero, and evaluating
  the two affine pieces.

## Remaining boundary

- Part (a): apply `Measure.integral_comp_mul_left` to the compiled scaling
  identity and reuse the dilation theorem; unit mass is now closed.
- Part (b): perform the two half-interval calculations and use a uniform
  first-order Taylor remainder to identify the limit as `-deriv φ 0`.
