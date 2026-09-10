# Sphere-cap height geometry

This module constructs the upper and lower height functions on the open unit
ball in `EuclideanSpace ℝ (Fin d)`:

`upper x = sqrt (1 - ‖x‖²)` and `lower x = -upper x`.

Open-ball membership gives a strictly positive radicand. Consequently the
upper height is strictly positive, the lower height is strictly negative, and
the square of the upper height is exactly `1 - ‖x‖²`.

The height functions are `C¹` on the open ball. The proof composes the smooth
norm-square function with square root where its argument is nonzero; the lower
result follows by negation. No derivative formula is asserted.

For each point in the domain, the literal `WithLp.toLp 2` graph points
`(x, upper x)` and `(x, lower x)` have squared norm one. These are metric
equalities in the actual L2 product. Dimension-two and dimension-three C1
examples compile for both signs, and all eleven audits use only standard
axioms.

The remaining work computes the derivatives and graph densities, constructs
the coordinate isometry to `EuclideanSpace ℝ (Fin (d+1))`, identifies the
actual graph images with strict sphere caps, and transports Hausdorff area.
This module contains no isometry, measure, normalization, equator, moment, or
consumer-closure claim.
