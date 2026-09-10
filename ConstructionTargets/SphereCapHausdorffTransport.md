# Ambient Hausdorff transport for strict sphere caps

This module transports the actual `d`-dimensional Hausdorff measure through the
reviewed coordinate isometry and derives exact ambient formulas for the two
literal strict Euclidean sphere caps.

`coordinate_hausdorff_image` applies
`IsometryEquiv.hausdorffMeasure_image` to the explicit map from the native L2
graph space to the appended-coordinate Euclidean space. Rewriting the reviewed
upper and lower Euclidean graph-image equalities then reduces each strict-cap
measure to the corresponding native graph measure.

The exact C1 graph-area theorem supplies the integral of the derivative
density. On the open unit ball, measurable-set integral congruence uses the
reviewed density formulas to replace that integrand by
`ENNReal.ofReal (1 / upper d x)`. The resulting formula holds without a
finiteness or numerical normalization assumption. Dimension-two and
dimension-three examples compile for both signs, and all three requested
audits use only standard axioms.

The remaining work identifies Hausdorff measure on each strict-cap subtype
with ambient Hausdorff measure of its underlying set, then exposes both forms
as the completed cap comparison. This module contains no intrinsic subtype
identification, numerical normalization, equator, moment, or consumer-closure
claim.
