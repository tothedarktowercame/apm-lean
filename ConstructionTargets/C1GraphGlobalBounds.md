# Exact C1 graph Hausdorff area

This module assembles the reviewed measurable C1 graph partition into an exact
Hausdorff-area equation for an actual `WithLp 2` graph. The domain is an open
subset of `EuclideanSpace ℝ (Fin d)`, the scalar function is `C¹` there, and
both sides use the existing `d`-dimensional Hausdorff measures. No finiteness
or integrability hypothesis is imposed.

For `0 < ε < 1`, each partition piece inherits the reviewed geometric graph
bounds and derivative-density comparisons. `integral_upper` and
`selected_integral_upper` compare the varying density integral with its
selected constant density. The lower estimate uses the explicit ENNReal
inequality `(1 - ε)(1 + ε) ≤ 1`; it neither divides nor cancels a possibly
zero or infinite value. `piece_global_bounds` therefore has exponents
`d + 1` on both error factors.

`global_bounds` substitutes the exact graph-measure and density-integral
countable decompositions and sums the piecewise inequalities. The result is
valid when either global value is zero or infinity. `exact_area` applies the
reviewed multiplicative squeeze theorem with exponent `d + 1`, entirely in
`ℝ≥0∞`. `exact_area_value` displays the density as
`ENNReal.ofReal (sqrt (1 + ‖fderiv ℝ f x‖²))`.

The empty-domain, zero-function, dimension-two, and dimension-three examples
compile, and all eleven theorem audits use only the standard axioms.

The remaining consumer work specializes this equation to the two actual
sphere-cap graphs, proves their measurable chart assembly, and determines the
Euclidean Hausdorff-to-volume normalization needed for literal sphere masses.
This module makes no numerical normalization, sphere-mass, Stokes, period, or
consumer-closure claim.
