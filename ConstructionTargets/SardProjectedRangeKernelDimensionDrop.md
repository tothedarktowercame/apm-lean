# Projected-range kernel dimension drop

`finrank_ker_rangeProjection_comp_lt` proves that projecting a nonzero
derivative onto its own range leaves a kernel whose real dimension is strictly
smaller than the source dimension. The proof shows that the projected map is
nonzero and then applies finite-dimensional rank–nullity.

This supplies the strict dimension decrease needed to invoke the
lower-dimensional induction hypothesis in an exact-rank projected chart.
