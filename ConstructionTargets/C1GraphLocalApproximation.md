# C1 local approximation balls

For any natural dimension `d`, let `f` be `ContDiffOn ℝ 1` on an open domain `U` in `EuclideanSpace ℝ (Fin d)`. At each `x ∈ U` and for every `ε > 0`, `local_ball` constructs a positive radius whose ball is contained in `U` and satisfies both derivative variation and two-point residual bounds relative to `fderiv ℝ f x`.

Continuity of the actual derivative on the open domain gives a neighborhood with derivative variation strictly below `ε`. Intersecting with `U` gives the ball. Differentiability at every point follows from C1 regularity and openness. The convex-ball mean-value theorem then proves

`‖f y - f z - fderiv ℝ f x (y-z)‖ ≤ ε * ‖y-z‖`.

`radius` chooses this proved radius. Its positivity, containment, derivative bound, residual bound, center membership and Borel measurability are exposed separately. No radius or uniform estimate is supplied as an assumption.

For `ε < 1`, `subset_bounds` applies `GraphMetricComparison.bounds` with `ell = fderiv ℝ f x` to every subset of the constructed ball. The graph retains the actual `WithLp 2` metric. The lower and upper Hausdorff factors are `ofReal (1-ε)^d` and `ofReal (1+ε)^d`, each multiplied by `ofReal (sqrt (1+‖fderiv ℝ f x‖²))`. All measure algebra remains in `ENNReal`; no measurability or finite-measure hypothesis is imposed on the subset, and zero and infinite measures remain covered.

Dimension-two and dimension-three examples and eleven standard-only axiom audits are included. The Lean file exactly matches the reviewed fixture SHA256 `558b8faca4c5dd128e8fa8db5bc4b1eb3e71ae14f881b5842299f15125fc199f`.

Countable selection of these balls, measurable disjointification, and measurability, disjointness and exact coverage of their actual graph images remain to be constructed. Passing to exact variable-density area equality, numerical sphere normalization and consumer closure is outside this module.
