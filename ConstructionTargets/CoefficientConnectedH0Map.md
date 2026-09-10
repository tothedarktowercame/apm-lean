# Connected H0 maps and S2 H1 vanishing over R

Promoted unchanged from `/tmp/CoefficientConnectedH0Map.lean`, SHA256 `d664b77de85b55eee08e1655625e99c3c37220907aac2033314da143a2d67c8f`.

R and spaces are Type 0; R is a commutative ring. For a continuous map between path-connected spaces, `mapIso_hom` identifies the actual induced H0 map with the isomorphism assembled from the source and target augmentation coordinates. `normalized_map` proves that source coordinate inverse, followed by the actual H0 map and target augmentation, equals identity on R.

For a path-connected ambient space and path-connected actual subtype A, the actual inclusion-induced H0 map is therefore invertible and its categorical kernel is zero. The module derives these connectivity hypotheses for the two-dimensional closed disk and its boundary: disk contractibility gives ambient connectivity, and the existing sphere geometry and boundary homeomorphism give subtype connectivity. It does not assert connectivity for the one-dimensional disk boundary.

The reviewed sphere-to-kernel isomorphism then yields `IsZero` for actual R-valued H1 of `ambientSphere 2`. Integer and rational specializations are included, along with ten standard-only axiom audits. Chains retain coefficient object `ModuleCat.of R R` throughout.

Dependencies are `CoefficientH0` and the reviewed `CoefficientSphereShift` (commit `0a94275eecb3e7a059de4816cb4a8b06c8d7e339`, PASS `invoke-1789014962618-17854-ab60e27b`).

Identifying the one-dimensional disk-boundary H0 inclusion with the codiagonal, applying its signed kernel normalization, and assembling circle H1 and S2 H2 remain downstream. This module claims neither those results nor general signed naturality or frozen consumer closure. No consumer placeholders change.
