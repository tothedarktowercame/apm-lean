# Proof Outline: m94A02

The frozen Lean theorem is present in `lean/Main.lean`. It is now proved that
the symmetric part vanishes whenever `A.transpose = -A`.
The symmetric part is also proved transpose-symmetric and Hermitian, both over
`ℝ` and after the scalar extension to `ℂ` used by the spectrum API.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94A02.md`

## Remaining boundary

- convert the supplied real-factor characteristic polynomial into the root
  multiset used by `Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`;
- use antitonicity to identify `σ` with the canonical ordered eigenvalues;
- translate the explicit complex `Matrix.mulVec` eigenvector equation into the
  Rayleigh quotient identity and apply the canonical extremal bounds.

Mathlib already contains the ordered-root reconstruction and Hermitian
Rayleigh machinery. No searched artifact packages the representation bridges.

Closer hop 3 proves that the complex scalar extension of a real
skew-symmetric matrix is skew-Hermitian, and separately compiles that `I • A`
is Hermitian. This isolates a route to the second conjunct without depending
on the arbitrary ordered family `σ`; the final eigenvector conversion remains
open.
