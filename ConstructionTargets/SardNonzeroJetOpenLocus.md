# Nonzero-jet open locus

This module promotes the neighborhood-localization step for the nonzero pieces
of the higher-jet decomposition.

If `f` is `ContDiff ℝ n` and `i ≤ n`, Mathlib's continuity theorem for
`iteratedFDeriv ℝ i f` makes the inverse image of the complement of `{0}`
open.  Thus the ambient locus where the `i`th derivative is nonzero is open.
The second theorem identifies the previously defined `nonzeroJetLocus f K i`
exactly as the intersection of an arbitrary source locus `K` with that open
ambient set.

No regularity is asserted for `K`, and no nullity conclusion is hidden in the
localization.  The next step is to select, at each point of this open locus, a
nonzero scalar or directional component of the jet and use its derivative-level
implicit-function hypersurface for the source-dimension reduction.  Those
local results must then be combined with flat-locus Taylor nullity before the
rectangular aggregation theorem applies.
