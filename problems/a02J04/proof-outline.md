# Proof Outline: a02J04

This proof outline was synthesized from legacy Lean files without a paired
proof-frame workspace.

Imported source: `lean-proofs/a02J04`

## Imported Lean Files

- `lean/Main.lean`

## Closer hop 1

The frozen theorem remains open. This hop establishes measurability of the
planar and proposed marginal densities, proves that the marginal density
vanishes outside `[0,1]`, and proves it is nonzero on `[0,1]` except at zero.

The remaining core calculation is Tonelli on the triangular vertical fibers:
the fiber over `x` is `[0,x]` when `x ∈ [0,1]`, hence has volume `x`, producing
density `2*x`. Once this marginal identity is formalized, the support and
positivity lemmas feed the absolute-continuity, mutual-singularity, and
reciprocal Radon–Nikodym calculations.
