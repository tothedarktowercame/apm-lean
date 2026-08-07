# Proof Outline: m01J03

The Lean artifact completes the compactness, top-eigenspace, finite-rank
projection, self-adjointness, positivity, and norm-one reductions. One spectral
gap/operator-norm convergence boundary remains.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m01J03.md`

## Formalized

- `T†T` is compact, self-adjoint, positive, and has norm one.
- The frozen kernel is its eigenvalue-one eigenspace.
- That eigenspace is finite-dimensional and has its canonical orthogonal
  projection, with the requested range and adjoint identities.

## Remaining Boundary

Restrict `T†T` to the orthogonal complement of the eigenvalue-one space, prove
its norm is strictly below one using compactness/Fredholm isolation, and deduce
geometric operator-norm convergence of its powers. Mathlib supplies the compact
self-adjoint eigenspace decomposition and Fredholm alternative, but no packaged
nonzero spectral isolation or power-to-projection theorem.
