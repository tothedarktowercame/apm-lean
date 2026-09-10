# Euclidean strict sphere-cap images

This module transports the reviewed native L2 strict caps and cap-height graphs
through the explicit coordinate isometry into literal subsets of the Euclidean
unit sphere.

The target upper and lower caps are subsets of
`Metric.sphere 0 1` in `EuclideanSpace ℝ (Fin (d+1))`, selected by a positive
or negative value at `Fin.last d`. Norm preservation and the last-coordinate
formula prove both forward image inclusions. The reverse inclusions use the
explicit inverse isometry; `symm_last` reconstructs the required sign exactly.

Combining these cap-image equalities with the reviewed native L2 graph
equalities proves that each upper or lower graph image is exactly its literal
Euclidean strict cap. Dimension-two and dimension-three examples compile for
both signs, and all six requested audits use only standard axioms.

The identification runs from the source native L2 graph and cap images under
the coordinate isometry to the target literal Euclidean strict-cap subsets,
with reverse membership reconstructed through the isometry inverse.

The remaining work proves preservation of the actual Hausdorff measure,
establishes the needed subtype-to-ambient measure identities, and combines
them with the exact graph-area and reciprocal-height density formulas. This
module contains no measure transport, normalization, equator, moment, or
consumer-closure claim.
