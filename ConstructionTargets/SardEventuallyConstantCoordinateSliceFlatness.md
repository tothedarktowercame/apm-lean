# Eventually constant-coordinate slice flatness

This module upgrades the constant-coordinate slice derivative lemmas to the
local form produced by an inverse chart.  If a coordinate composed with a
slice agrees eventually with a constant near the base point, derivative
uniqueness forces the coordinate derivative composed with the slice derivative
to vanish.

`hasFDerivAt_zero_on_eventuallyConstantCoordinateSlice` then combines this
kernel tangency with a residual derivative that vanishes on the coordinate
kernel.  The residual map restricted to the slice has zero Fréchet derivative
at the base point.

The next consumer specializes the eventual equality to fixed
derivative-range-coordinate slices in the explicit projected inverse-chart
neighborhood, uses rank-at-most residual flatness, and derives local image
nullity for each order-one exact-rank piece.
