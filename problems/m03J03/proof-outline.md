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

## Hop 4 bridge contracts

- `apm_m03J03_bridge_dirac_comb` states the locally finite one-sided Dirac
  comb as an LF-continuous distribution.
- `apm_m03J03_bridge_polynomial_fourier_series` states the distributional
  Fourier-series constructor under the frozen polynomial-growth hypothesis.
- `apm_m03J03_bridge_heaviside_sin_distributions` states all three regular
  functionals for `H*sin`, including their LF-continuity and the missing
  second half-line identity with its Dirac boundary term.

These declarations are intentionally unproved. Together with the compiled
absolute-value non-example, they reduce the main theorem to conjunction
assembly without modifying its frozen statement.
