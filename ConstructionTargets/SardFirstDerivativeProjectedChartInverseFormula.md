# First-derivative projected chart inverse formula

`exists_projected_localRankNormalForm_with_inverse_formula` retains the full
local coordinate behavior of the projected rank chart.

It exposes the exact forward coordinate formula and, eventually near the base
coordinate, proves that applying the inverse chart and then either projected
coordinate returns the corresponding product coordinate. The base point is
also retained in the chart source.

The remaining consumer step restricts these eventual identities to an explicit
neighborhood, differentiates constant first-coordinate slices, and combines
their kernel tangency with residual derivative flatness.
