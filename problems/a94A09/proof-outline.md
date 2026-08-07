# Proof Outline: a94A09

The boundary-nonvanishing part of the straight-line homotopy is now compiled
as `apm_a94a09_homotopy_ne_zero`. One `sorry` remains in the main theorem.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a94A09.md`

## Completed

- For every `t ∈ [0,1]`, `z - t f(z)` is nonzero on the unit circle. For
  `t < 1` this follows from the norm estimate; at `t = 1` it is precisely the
  no-boundary-fixed-point hypothesis.

## Open boundary

`ConstructionTargets.Rouche.zeroCountInClosedBall_add_eq` now supplies strict
Rouché transfer, but requires `AnalyticOnNhd` on the closed disk. The frozen
theorem assumes only `ContinuousOn` the closed disk and `DifferentiableOn` the
open disk, and its boundary inequality is non-strict. Closure needs either:

- an argument-principle/zero-count theorem for this boundary-continuous,
  interior-holomorphic setting and invariance along the compiled homotopy; or
- a shrink-radius and `t → 1` limiting argument with Hurwitz-style zero
  persistence, followed by Schwarz equality to prove uniqueness.
