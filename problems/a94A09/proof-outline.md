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

## Closer hop 3

The boundary analyticity mismatch can be routed around without changing the
statement. For `0 ≤ t < 1`, choose `t < r < 1`. Then `f` is analytic on a
neighborhood of `closedBall 0 r`, and `‖t * f z‖ < ‖z‖` on `sphere 0 r`, so
strict Rouché applies to `z - t * f z`. A sequence `t → 1`, followed by
compactness and continuity, would yield a fixed point at the endpoint.

Two concrete library interfaces are still absent:

- the Rouché module proves equality of divisor sums but does not export the
  identity-map count or extraction of a zero from a nonzero count;
- uniqueness needs the disk automorphism `(z-a)/(1-conj(a)z)` and its inverse,
  while Mathlib only packages Möbius actions for the upper half-plane.

These are now the exact remaining local developments.

## Hop 4: zero-count interface closed

The formerly missing Rouché interfaces are now proved locally. The polynomial
divisor count is identified with the filtered root multiset (reusing the
compiled argument from `a92J05`), which gives
`apm_a94a09_zeroCount_id`. Independently,
`apm_a94a09_exists_zero_of_zeroCount_ne_zero` shows directly from the divisor
definition that a nonzero analytic count forces a zero in the closed ball.
`apm_a94a09_exists_zero_id_add_of_rouche` combines both with the exported
strict Rouché theorem.

The main theorem remains open beyond this assigned interface: applying the new
existence lemma along radii and parameters approaching one requires the
compactness/continuity limit assembly, and uniqueness still requires the disk
Möbius conjugation and Schwarz equality argument.
