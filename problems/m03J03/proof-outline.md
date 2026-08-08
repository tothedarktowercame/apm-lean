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

## Remaining boundary

- construct the locally finite one-sided Dirac comb as an LF-continuous map;
- construct polynomial-growth Fourier series as distributions using repeated
  integration by parts and summability;
- bundle the regular distribution for `H sin` and prove both half-line
  integration-by-parts identities identifying its first two derivatives.
