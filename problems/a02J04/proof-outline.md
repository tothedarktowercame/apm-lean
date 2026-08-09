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

## Hop 4 bridge contracts

- `apm_a02J04_bridge_restrict_absolutelyContinuous` states the reverse
  absolute-continuity consequence of positivity away from the null singleton
  `{0}`.
- `apm_a02J04_bridge_compl_mutuallySingular` states the singularity consequence
  of the density vanishing outside `[0,1]`.
- `apm_a02J04_bridge_rnDeriv` states the exact reciprocal-density
  specialization of `Measure.rnDeriv_withDensity_right`.

These declarations are intentionally unproved. Together with the compiled
marginal identity, they reduce `apm_a02j04` to conjunction assembly while
leaving its frozen statement untouched.
