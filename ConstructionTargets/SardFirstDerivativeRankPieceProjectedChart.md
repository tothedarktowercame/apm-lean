# First-derivative rank-piece projected chart

`exists_open_rankUpperLocus_and_projected_localRankNormalForm` packages the two
local structures needed at a point of an order-one exact derivative-rank piece.

It retains an open neighborhood on which the localized exact-rank locus equals
its rank-at-most form. At the same base point it constructs the projected local
rank `OpenPartialHomeomorph`, whose coordinates are the range of the base
derivative and the kernel of the derivative followed by projection onto that
range.

The remaining consumer step is to retain the chart coordinate formulas, prove
residual derivative flatness on constant projected-coordinate slices, and
derive local image nullity for the exact-rank piece.
