# Countable C1 graph approximation partition

For any natural dimension `d`, an open subset `U` of `EuclideanSpace ℝ (Fin d)`, a function `ContDiffOn ℝ 1 f U`, and `ε > 0`, this module constructs countably many pairwise disjoint Borel pieces with union exactly `U`.

For nonempty `U`, the reviewed `C1GraphLocalApproximation.radius` supplies an open approximation ball at each point. The hereditary Lindelof property selects a countable subcover. `disjointed` makes these balls disjoint while preserving measurability, coverage and containment in the selected ball. Each associated functional is the actual derivative at the selected ball center in `U`. Derivative proximity and the two-point residual bound restrict from that ball to its piece; the pieces themselves need not be convex. For empty `U`, the existence proof uses empty pieces and zero functionals, without selecting a point. `empty_pieces` verifies that the packaged choices are empty as well.

The graph sets retain `GraphMetricComparison.Graph` in the actual `WithLp 2` ambient space. The reviewed `GraphMetricComparison.graph_image` identifies these sets with literal images of the graph map. To prove measurability, extend `f` by zero outside `U`; this extension is measurable by continuity on `U` and its measurable complement. On each measurable subset of `U`, the graph is exactly the intersection of the first-coordinate preimage of the subset and the equality set between the second coordinate and the extension applied to the first. Coordinate continuity supplies measurability. No graph-image measurability is assumed.

Graph disjointness follows from first-coordinate disjointness. The graph operation commutes with the countable union, yielding exact graph coverage. For `ε < 1`, `piece_bounds` applies the reviewed two-sided L2 Hausdorff bounds to the constructed residual estimate and selected derivative functional. The ENNReal bounds impose no finite-measure assumption and retain zero and infinite measures.

The module includes dimension-two and dimension-three bound examples and eighteen standard-only axiom audits. Its Lean source is identical to the reviewed fixture SHA256 `26d94f98e9f8997ad4e56b9c1cf75951c59a8b65cacf0e93e8807398642f1f1d`.

Exact variable-density area equality remains to be deduced from these measurable approximation pieces and derivative-density control. Sphere-chart assembly and numerical Euclidean Hausdorff normalization remain downstream. This module claims no sphere mass or frozen consumer closure.
