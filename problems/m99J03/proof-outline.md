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

## Remaining boundary

- Part (a): reduce the raw piecewise Lebesgue integral to
  `[-1/n,1/n]`, normalize it, and control `φ x - φ 0` uniformly.
- Part (b): perform the two half-interval calculations and use a uniform
  first-order Taylor remainder to identify the limit as `-deriv φ 0`.
