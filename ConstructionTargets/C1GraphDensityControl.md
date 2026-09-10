# C1 graph-density control

`C1GraphDensityControl` defines graph density on an arbitrary real normed additive commutative group as the actual L2 product norm

`density x = ‖WithLp.toLp 2 ((1 : ℝ), x)‖`.

The L2 product identity proves `density x ^ 2 = 1 + ‖x‖ ^ 2`, hence the usual square-root formula. Projection to the real coordinate proves `1 ≤ density x`. Comparing the two L2 vectors `(1,x)` and `(1,y)` proves the reverse-triangle estimate

`|density x - density y| ≤ ‖x-y‖`.

Thus density is 1-Lipschitz and continuous. Composing with continuous `ENNReal.ofReal` gives the continuous ENNReal-valued density and, when the space carries its Borel measurable structure, its measurability.

If `0 ≤ ε` and `‖x-y‖ ≤ ε`, the Lipschitz estimate and the lower bound by one give real multiplicative bounds with factors `1-ε` and `1+ε`. Applying `ofReal` gives the corresponding ENNReal inequalities. When `ε > 1`, the lower factor maps to zero explicitly, so no invalid subtraction or positivity premise is introduced. No finite-dimensionality or measure hypothesis is used.

For continuous linear functionals on `EuclideanSpace ℝ (Fin d)`, `functional_density_eq` identifies this L2 construction with `sqrt (1 + ‖A‖²)`. Dimension-two and dimension-three examples and eleven standard-only axiom audits are included. The Lean source is byte-identical to the reviewed fixture SHA256 `52879bd1fed15c508c3cf9e31cfb1ae8172fdf31414a3ccfe9cd655d438b7a2c`.

The remaining area step must apply derivative proximity on every reviewed partition piece, integrate these density inequalities, sum the disjoint piece bounds, and invoke the reviewed ENNReal multiplicative squeeze. This module proves no global integral bound, graph-area formula, numerical Hausdorff normalization, sphere mass, Stokes theorem, period result, or consumer closure.
