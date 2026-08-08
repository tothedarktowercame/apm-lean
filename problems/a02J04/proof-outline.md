# Proof Outline: a02J04

This proof outline was synthesized from legacy Lean files without a paired
proof-frame workspace.

Imported source: `lean-proofs/a02J04`

## Imported Lean Files

- `lean/Main.lean`

## Closer hop 2

The frozen theorem remains open. Hop 1 established measurability of the
planar and proposed marginal densities, proves that the marginal density
vanishes outside `[0,1]`, and proves it is nonzero on `[0,1]` except at zero.

Hop 2 proves the vertical-section measure formula and the complete pointwise
inner Tonelli identity
`∫⁻ y, g (x,y) = ofReal (tauDensity x)` for every real `x`.

The remaining core calculation is the measure-level Tonelli/map extensionality
step using this identity. Once the marginal equality is formalized, the support and
positivity lemmas feed the absolute-continuity, mutual-singularity, and
reciprocal Radon–Nikodym calculations.
