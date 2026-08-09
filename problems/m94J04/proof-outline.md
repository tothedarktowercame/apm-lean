# Proof Outline: m94J04

The frozen Lean theorem is present in `lean/Main.lean`. Coordinate inner-product
reductions were already proved; the two scalar coefficient branches are now
also available as named lemmas.
The ambient-to-slice derivative identity is now compiled for every coordinate
line and every component of a test function.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-m94J04.md`

## Remaining boundary

- transport Euclidean volume through
  `EuclideanSpace.volume_preserving_measurableEquiv_toLp`;
- split the raw `Fin 3 → ℝ` coordinate function using
  `MeasurePreserving.piFinSuccAbove`;
- transport compact support and integrability to slices, integrate by parts,
  and reassemble by Fubini.

The ambient divergence and line-derivative integration-by-parts theorems do
not apply directly across the discontinuity at `x = 0`.

Closer hop 3 proves that each affine coordinate-line parametrization is an
isometry. Consequently the missing slice-support result can be approached as
compact-preimage transport along a proper embedding; the remaining work is
to connect that fact to the explicit coordinate measure equivalences and
Fubini.

## Hop 4: stated bridge

`apm_m94J04_bridge_1` now states the exact remaining scalar integral identity.
It is obtained from the main theorem by the already-compiled inner-product
reductions, but its mathematical content is specifically the missing measure
transport, Fubini split, and fiberwise integration-by-parts calculation. The
bridge is deliberately left unproved for the dedicated follow-up task.
