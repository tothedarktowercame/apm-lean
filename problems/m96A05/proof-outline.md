# Proof Outline: m96A05

The Lean artifact proves the linear-algebra uniqueness reduction and the
strict lower bound on every diagonal entry. Two finite-row assembly boundaries
remain.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m96A05.md`

## Formalized

- A nonzero determinant gives a unique discrete solution.
- Every mesh point belongs to `[0,1]`.
- If `b < 0` on `[0,1]`, every diagonal entry has norm strictly greater than
  two, for every positive mesh size.

## Remaining Boundary

- Expand the three-supported tridiagonal row sum to identify the stencil and
  matrix equations, including endpoint rows.
- Bound `a` on the compact interval, choose an eventual mesh threshold making
  both neighbor coefficients nonnegative, and prove the erased off-diagonal
  row sum is at most two before applying Gershgorin.
