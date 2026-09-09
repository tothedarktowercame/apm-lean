# Positive-rank stratum assembly with open-domain induction

This module propagates the reviewed open-domain slice contract to nullity of
the actual positive deficient-rank stratum for globally genuine-infinity
smooth maps between finite-dimensional complete real inner-product sources
and finite-dimensional real inner-product targets with Borel Haar measure.

The sole induction premise asserts critical-image nullity on subsets of
explicitly open domains where the map is ContDiffOn real infinity, for all
strictly smaller complete finite-dimensional inner-product sources. This
includes dimension zero. It does not request pointwise infinity on arbitrary
sets.

`SardOpenContractCompactProbe.exists_compact_positive_rank_image_null` invokes
`SardPositiveRankSliceOpenInductionContract` for the actual chart. It places
each fixed-coordinate source fiber of a compact rank-bounded set into the
actual residual slice subset, using the chart's first-coordinate identity
and inverse law. Existing compact coordinate-fiber nullity applies Fubini
and transports through the target orthogonal linear equivalence. Borel and
topology packages are derived; continuity follows from global smoothness.

`SardOpenContractChartProbe.exists_open_rank_upper_image_null` derives
closedness of the rank-upper locus and uses the existing countable compact
exhaustion of its intersection with the actual open chart source. Every
compact subset inherits source containment and its rank bound. Countable
image-null assembly yields open-chart rank-upper nullity.

`SardPositiveRankStratumOpenContractAssemblyProbe.measure_image_zero_positive_rank_stratum`
constructs these neighborhoods at each exact rank-stratum point, chooses
coordinate Haar measures with inherited Borel/topology data, restricts
rank-upper nullity to the exact stratum, and applies the existing pointwise
open aggregation with derived second countability.

`measure_image_zero_positive_rank_stratum_of_global_induction` supplies the
exact open-domain premise using the reviewed localization compatibility
producer from smaller-dimensional global smooth critical-image nullity.

All chart construction and generic measure infrastructure are reused.
Existing stronger-premise APIs remain unchanged. This is conditional
positive-rank nullity only: rank-zero first-nonzero-jet contract repair,
compatible global/local induction discharge, base cases and manifold
transport remain before unconditional Sard or any frozen consumer closure.
