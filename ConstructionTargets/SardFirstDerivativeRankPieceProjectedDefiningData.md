# First-derivative rank-piece projected defining data

`exists_open_rankUpperLocus_and_projected_definingData` retains the complete
defining packet for projected local rank coordinates at an order-one exact-rank
point.

Alongside the open neighborhood where the localized exact-rank piece equals
its rank-at-most form, the theorem exposes the base derivative range, the
projected left coordinate, the orthogonal kernel coordinate, their strict
derivatives, surjective ranges, and complementary kernels. These are precisely
the fields needed to construct the corresponding `ImplicitFunctionData`.

The remaining consumer step is to construct that exact chart, retain its
coordinate formulas, and prove residual derivative flatness on its constant
projected-coordinate slices before local image-nullity aggregation.
