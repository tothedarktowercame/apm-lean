# Proof Outline: m93A01

The frozen theorem has a partial Lean development with one remaining `sorry`.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m93A01.md`

## Compiled progress

- `apm_m93A01_not_compact_of_separated_unit` proves the generic sequential
  obstruction used by both noncompactness clauses.
- `apm_m93A01_norm_single` proves the standard Fourier coordinate vectors are
  unit vectors.
- `apm_m93A01_diagonal_single` computes the action of any operator satisfying
  a pinned diagonal identity on those coordinate vectors.
- `apm_m93A01_norm_diagonal_single` identifies the norm of each such image
  with the norm of the corresponding scalar symbol.
- `apm_m93A01_not_compact_of_pos_separated_unit` permits any positive uniform
  separation constant.
- `apm_m93A01_circleDerivH1Coeff_lower` proves the `D1` multiplier has norm at
  least `1/2` on positive integer frequencies.
- `apm_m93A01_circleDerivH1_not_compact` closes the entire `D1`
  noncompactness clause by evaluating each image difference at one coordinate.

## Remaining boundary

- construct finite-coordinate truncations on `lp (fun _ : ℤ ↦ ℂ) 2`, prove
  finite rank, and establish operator-norm convergence for the two decaying
  symbols;
- build normalized functions on disjoint positive-measure sets whose `ιR`
  images remain uniformly separated.
