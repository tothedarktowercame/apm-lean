# Proof Outline: m03J03

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m03J03.md`

## Compiled progress

- `m03J03_abs_eval_not_distribution` proves the complete fourth conjunct by
  evaluating a hypothetical linear distribution on a smooth bump and its
  negation.
- `m03J03_integral_heaviside_mul` converts every Heaviside-weighted whole-line
  integral exactly to a set integral over `Ioi 0`, preparing both derivative
  identities for Mathlib's improper integration-by-parts API.
- `m03J03_heaviside_sin_integral_deriv` applies the compact-support endpoint
  theorem to `sin · φ` and proves `-∫ H sin φ' = ∫ H cos φ` without explicit
  endpoint-limit bookkeeping.

## Remaining boundary

- construct the locally finite one-sided Dirac comb as an LF-continuous map;
- construct polynomial-growth Fourier series as distributions using repeated
  integration by parts and summability;
- prove the second half-line identity and bundle all three regular functionals
  as LF-continuous distributions.
