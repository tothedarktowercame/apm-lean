# Finite intrinsic measure of sphere caps

This module proves finite top-dimensional Hausdorff measure for the actual
cap domain and cap image constructed in `SphereCapGraph`. The general
ambient space is a finite-dimensional real inner-product space with its
Borel measurable structure.

`plane e` is the orthogonal complement of the span of `e`.
`domainBallIsometry e r` identifies `capDomain e r` with the closed
radius-`r` ball in `plane e`. Both directions preserve the underlying ambient
vector; the orthogonality and norm conditions supply the subtype witnesses.
The inverse laws and preservation of distance follow directly.
This isometry itself requires neither finite dimension nor a unit vector.

`domain_measure_eq` combines that isometry with the isometric inclusion of
the closed-ball subtype into the plane. For every real `d ≥ 0`, it proves
equality between Hausdorff measure of the whole cap-domain subtype and
Hausdorff measure of the closed ball as a subset of the plane. Finite
dimension is not required for this equality.

For `domain_measure_finite`, the exponent is `finrank ℝ (plane e)`.
Orthonormal coordinates give an isometry into the corresponding Euclidean
space. The closed ball is compact, its coordinate image is compact, and
top-dimensional Hausdorff measure of that image is finite. Transporting
measure back proves finiteness on the actual cap domain.

Under `a > 0`, `0 ≤ r < 1`, `a² ≤ 1 - r²`, and `‖e‖ = 1`,
`cap_measure_finite` combines this result with the banked Lipschitz image
bound. The factor `(1 + r/a)^d` is finite, so the image of the actual
`capMap` has finite intrinsic Hausdorff measure on the literal unit sphere
subtype.

For `e : EuclideanSpace ℝ (Fin (d + 1))`, the unit-vector hypothesis makes
`e` nonzero, and the orthogonal complement has dimension `d`.
`euclidean_cap_measure_finite` therefore obtains the required exponent.
`dimension_two` and `dimension_three` specialize this result to caps on
the unit spheres in Euclidean spaces of dimensions three and four.

The remaining consumer work is to construct finitely many signed coordinate
cap images covering each entire sphere, sum the finite measure bounds, and
derive integrability for the exact flux polynomial and projective-sphere
mixed and square summands. This module does not establish finite coverage,
whole-sphere finiteness, global integrability, measure normalization, or
numerical moments. No normalization theorem is needed for this finiteness
step.

The source is an unchanged promotion of
`/tmp/SphereCapFiniteMeasureProbe.lean`, SHA-256
`fc88ca53846907636b0525ae218b65c62687c72542caacf1d8af6c1275d822a3`.
The cap-graph dependency was independently reviewed PASS at commit
`3d5d18e79f87b0d9cd0716183976b59529f7ab14`.
Validation compiles the fixture and canonical target, builds this module
with `SphereCapGraph`, and reproduces all seven printed axiom audits.
The permitted axioms are `propext`, `Classical.choice`, and `Quot.sound`.
