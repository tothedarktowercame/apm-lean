# Proof Outline: a94A09

The boundary-nonvanishing part of the straight-line homotopy and the
maximum-modulus disk-self-map reduction are now compiled as
`apm_a94a09_homotopy_ne_zero` and `apm_a94a09_mapsTo_closedBall`. One `sorry`
remains in the main theorem.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a94A09.md`

## Completed

- For every `t ∈ [0,1]`, `z - t f(z)` is nonzero on the unit circle. For
  `t < 1` this follows from the norm estimate; at `t = 1` it is precisely the
  no-boundary-fixed-point hypothesis.
- The boundary inequality propagates to every point of `closedBall 0 1` by
  `Complex.norm_le_of_forall_mem_frontier_norm_le`; thus `f` maps the closed
  unit disk to itself. This closes the maximum-modulus interface needed by a
  future Schwarz-based uniqueness proof.

## Open boundary

`ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq` now supplies strict
Rouché transfer, but requires `AnalyticOnNhd` on the closed disk. The frozen
theorem assumes only `ContinuousOn` the closed disk and `DifferentiableOn` the
open disk, and its boundary inequality is non-strict. Closure needs either:

- an argument-principle/zero-count theorem for this boundary-continuous,
  interior-holomorphic setting and invariance along the compiled homotopy; or
- a shrink-radius and `t → 1` limiting argument with Hurwitz-style zero
persistence, followed by Schwarz equality to prove uniqueness.

Mathlib's current Schwarz lemmas provide contraction bounds and an affine
equality case for maps between balls, but do not package the disk-automorphism
conjugation needed to move an arbitrary fixed point to zero. More importantly,
they do not establish existence at the non-strict endpoint; zero-count
invariance or a Hurwitz/compactness argument is still required first.
