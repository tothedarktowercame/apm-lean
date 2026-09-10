# Countable graph-measure and density-integral decomposition

`C1GraphMeasureDecomposition` works with the actual `d`-dimensional Hausdorff measures on `EuclideanSpace ℝ (Fin d)` and on its `WithLp 2` graph ambient space. It assumes an open domain `U`, a function `ContDiffOn ℝ 1 f U`, and a positive approximation parameter.

The ENNReal-valued density at `x` is `ofReal` of the actual L2 density of `fderiv ℝ f x`. Its value is `ofReal (sqrt (1 + ‖fderiv ℝ f x‖²))`. Continuity of the derivative on the open domain, composed with the reviewed continuous density, proves continuity on `U`.

The reviewed partition has measurable, pairwise-disjoint domain pieces and measurable, pairwise-disjoint graph images with exact unions. Countable additivity therefore gives exact decompositions of both the graph Hausdorff measure and the derivative-density lintegral. These equations need no finiteness or integrability assumptions.

On each piece, the integral of its selected constant derivative density is exactly that density times the piece's Hausdorff measure. The reviewed derivative-proximity estimate and ENNReal density-control theorem compare the varying density with the selected density in both required directions. The reverse comparison uses symmetry of the norm difference. No ENNReal value is cancelled or converted to a real number.

Dimension-two and dimension-three examples and nine standard-only axiom audits are included. The Lean source is byte-identical to the reviewed fixture SHA256 `de4423dbec32306d4c5191a7b165dbf09dd446d3c76f52584b619ae9dda421af`.

The remaining step must combine these exact decompositions with the reviewed piecewise graph bounds, integrate the density comparisons, sum the inequalities, and invoke the ENNReal multiplicative squeeze. This module proves no summed global bounds, exact graph area, numerical Hausdorff normalization, sphere mass, Stokes theorem, period result, or consumer closure.
