# Strict sphere-cap images in the L2 graph space

This module identifies the reviewed upper and lower sphere-height graphs with
strict unit caps in their native ambient space
`WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)`.

The upper cap consists of points with norm one and positive last coordinate;
the lower cap uses a negative last coordinate. The graph-to-cap inclusions use
the reviewed literal L2 squared-norm equations and strict height signs.

For the reverse inclusions, the L2 product norm equation and the nonzero last
coordinate force the first coordinate into the open unit ball. The unit-norm
equation then reconstructs the last coordinate as the signed square root. This
gives exact set equalities for both signs. Dimension-two and dimension-three
examples compile, and all six requested audits use only standard axioms.

The remaining work constructs the explicit linear isometric equivalence from
this L2 product to `EuclideanSpace ℝ (Fin (d+1))`, proves its coordinate and
literal Euclidean-cap image formulas, and transports the reviewed exact graph
area. This module contains no Euclidean isometry, subtype or Hausdorff
transport, normalization, equator, moment, or consumer-closure claim.
