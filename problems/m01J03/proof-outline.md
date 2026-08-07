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

Closer hop 3 identifies a shorter route that avoids proving general spectral
discreteness. `CStarAlgebra.norm_or_neg_norm_mem_spectrum` supplies an extremal
real spectral value for the self-adjoint compact operator `S-P`. If its norm
were one, compact Fredholm alternative should turn the resulting `±1`
spectral point into an eigenvector. The projection identities put that vector
in `ker P`; positivity excludes `-1`, while `+1` belongs to the top eigenspace
and is therefore fixed by `P`, contradicting membership in its kernel.
`spectrum.algebraMap_mem 𝕜` closes transport of the real spectral witness to
the `RCLike` spectrum. The remaining formal bridge is the local `±1`
eigenvector/positivity contradiction.
