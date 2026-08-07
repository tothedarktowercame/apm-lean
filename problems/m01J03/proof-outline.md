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
- The square fixes that projection on both sides: `S.comp P = P` and
  `P.comp S = P`.
- A local normed-ring lemma proves that these identities, idempotence, and the
  single estimate `‖S - P‖ < 1` imply `S ^ n → P` in norm.

## Remaining Boundary

Prove the now-isolated estimate `‖T†T - P‖ < 1`. This is the nonzero spectral
isolation theorem for a compact operator, specialized to the positive
self-adjoint contraction and its eigenvalue-one projection. Mathlib supplies
the compact self-adjoint eigenspace decomposition, finite nonzero eigenspaces,
and Fredholm alternative, but no packaged discreteness/isolation theorem for
the nonzero spectrum. The geometric operator-norm convergence after this
estimate is complete.
