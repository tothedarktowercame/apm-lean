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
- `apm_m97a04_extend_center`, `apm_m97a04_extend_zero`, and
  `apm_m97a04_extend_succ_boundary` compile the center-grid and homogeneous
  endpoint evaluations needed by the stencil.
- `apm_m97a04_neighbor_norm_sum` proves the two possible off-diagonal norms
  sum to exactly two under the eventual mesh-smallness inequality.
- `apm_m97a04_matrix_diag`, `apm_m97a04_matrix_pred`, and
  `apm_m97a04_matrix_succ` compute all three possible nonzero row entries,
  including the dependent predecessor/successor indices.

## Remaining boundary

- Prove the exact contract `apm_m97a04_mulVec_eq_stencil` recorded in the
  boundary comment, collapsing each `Matrix.mulVec` row to its at-most-three
  supported entries.
- Prove `apm_m97a04_erased_row_norm_sum_le_two`, also recorded there, by the
  same dependent-index collapse and `apm_m97a04_neighbor_norm_sum`.
- Bound `a` on `[0,1]`, choose an eventual mesh threshold satisfying the
  second contract's hypothesis, and apply
  `Matrix.det_ne_zero_of_sum_row_lt_diag`.
