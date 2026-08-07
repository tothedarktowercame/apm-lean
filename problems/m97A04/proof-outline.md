# Proof Outline: m97A04

The canonical Lean attempt is `lean/Main.lean`. It now contains the principal
matrix reductions, with the finite supported-sum assembly still open.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m97A04.md`

## Compiled progress

- `apm_m97a04_matrix_eq_zero_of_not_neighbor` proves exact tridiagonal row
  support.
- `apm_m97a04_unique_mulVec_of_det` proves that a nonzero determinant gives a
  unique solution for every right-hand side.
- `apm_m97a04_diagonal_norm_gt_two` proves the diagonal norm is strictly
  greater than two whenever `b < 0` on `[0,1]`.

## Remaining boundary

- Collapse each `Matrix.mulVec` row sum to its at-most-three supported entries
  and identify the endpoint values of `apm_m97a04_extend`.
- Bound `a` on `[0,1]`, choose an eventual mesh threshold making both neighbor
  coefficients nonnegative, prove the erased-row norm sum is at most two, and
  apply `Matrix.det_ne_zero_of_sum_row_lt_diag`.
