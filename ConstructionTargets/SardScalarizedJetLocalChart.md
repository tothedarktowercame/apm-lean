# Scalarized jet local chart

This module combines the strict-derivative promotion with the exact
implicit-function-data construction.

For a `C^(i+1)` map and a selected scalar component of the next jet that is
nonzero on `Fin.cons h v`, the scalarized fixed-direction `i`-jet has the
required strict derivative automatically. The resulting open partial
homeomorphism has target `ℝ × ker L`, where `L` is the exact `fderiv` of
`y ↦ ℓ (iteratedFDeriv ℝ i f y v)`, contains the basepoint in its source, and
maps it to the expected scalar and orthogonal kernel coordinates.

Using these local hypersurface coordinates for source-dimension nullity and
aggregating the nonzero-jet strata remain downstream.
