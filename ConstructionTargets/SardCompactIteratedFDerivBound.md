# Compact iterated Fréchet-derivative bound

`exists_nonneg_norm_iteratedFDeriv_le_on_compact` gives a single nonnegative
real constant bounding the norm of a fixed-order iterated Fréchet derivative
at every point of a compact set. The derivative order is required to lie within
the supplied global `ContDiff` regularity.

The proof uses continuity of `iteratedFDeriv`, compact boundedness of its norm
image, and `max M 0` to retain an explicitly nonnegative bound. It preserves
the fixture's compactness and differentiability hypotheses and uses only
standard axioms.

The remaining consumer work is to construct a compact set containing every
source segment, apply this bound at order `k + 1`, use the multilinear-map norm
inequality to get the scaled affine-line derivative bound, and feed
`affineLine_flat_taylor_remainder_bound` into
`exists_taylor_cover_measure_lt`.
