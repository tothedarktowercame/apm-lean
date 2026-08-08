# Proof Outline: a02J04

This proof outline was synthesized from legacy Lean files without a paired
proof-frame workspace.

Imported source: `lean-proofs/a02J04`

## Imported Lean Files

- `lean/Main.lean`

## Closer hop 3

The frozen theorem remains open. Hop 1 established measurability of the
planar and proposed marginal densities, proves that the marginal density
vanishes outside `[0,1]`, and proves it is nonzero on `[0,1]` except at zero.

Hop 2 proves the vertical-section measure formula and the complete pointwise
inner Tonelli identity
`∫⁻ y, g (x,y) = ofReal (tauDensity x)` for every real `x`.

`apm_a02J04_tau_eq_withDensity` now completes the measure-level Tonelli and
map-extensionality calculation, proving that the pushforward is exactly the
proposed `withDensity` measure.

The remaining work is to feed the compiled support and positivity facts into
absolute continuity and mutual singularity, handle the null exceptional point
`{0}`, and specialize `Measure.rnDeriv_withDensity_right` to the displayed
reciprocal density.
