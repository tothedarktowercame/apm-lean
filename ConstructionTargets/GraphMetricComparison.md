# Uniform graph Hausdorff bounds

`GraphMetricComparison` compares graphs in the actual `WithLp 2` ambient space over `EuclideanSpace ℝ (Fin d)`. It applies in every natural dimension to an arbitrary set `s`, scalar function `f`, and continuous linear functional `ell`. Its explicit hypothesis is

`‖f x - f y - ell (x - y)‖ ≤ ε * ‖x - y‖` for `x,y ∈ s`, with `0 ≤ ε < 1`.

The coordinate-preserving equivalence between the linear and nonlinear graph subtypes is constructed with both inverse laws. The residual estimate gives forward Lipschitz constant `1 + ε` and inverse constant `1 / (1 - ε)`, hence a constructed homeomorphism. These estimates use the L2 product norm.

Subtype inclusion identifies intrinsic Hausdorff measure with the ambient graph-image measure. Applying the two actual Lipschitz maps and the reviewed `LinearGraphDensity.image_measure` gives

`ofReal (1-ε)^d * ofReal (sqrt (1+‖ell‖²)) * H_d(s) ≤ H_d(graph(f,s))`

and

`H_d(graph(f,s)) ≤ ofReal (1+ε)^d * ofReal (sqrt (1+‖ell‖²)) * H_d(s)`.

All factors and measures in these inequalities are in `ENNReal`. The lower bound multiplies the inverse inequality by the positive finite factor `ofReal (1-ε)^d`, then uses the reciprocal scalar identity. It never cancels a measure, so zero and infinite measures are included. No measurability, openness, differentiability, finite-measure or nonzero-functional hypothesis is imposed.

The module includes empty-set, zero-error, zero-functional, dimension-two and dimension-three examples, and twenty axiom audits. The Lean source is promoted byte-for-byte from the reviewed fixture with SHA256 `6b58f18ef2b8e95e6b8a1b3b82fba13ff770c16950a4cbf0202a6cf542a21779`.

The remaining area argument must partition differentiable graphs into measurable approximation pieces and establish exact density equality. Sphere-chart measure assembly and numerical Euclidean Hausdorff normalization remain downstream. This theorem supplies no nonlinear area formula, sphere mass, Stokes or period conclusion, or frozen consumer closure.
