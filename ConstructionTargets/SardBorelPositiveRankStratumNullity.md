# Borel positive-rank stratum nullity

`SardBorelPositiveRankStratumNullityProbe.measure_image_zero_of_positive_rankStratum_finiteOrder` proves zero target add-Haar measure of the image of an entire exact positive-rank stratum, assuming every point of that stratum is critical.

The map has global regularity of a positive finite order and satisfies classical admissibility. Source and target are finite-dimensional real inner-product spaces; source completeness and second countability and target Borel compatibility are explicit. Borel-compatible classical nullity at every dimension below the exact source dimension remains an induction premise. Neither local neighborhoods nor chart certificates are supplied as premises.

The proof directly invokes `SardBorelPositiveRankPointwiseClosedOpenNullityProbe.exists_open_rankUpper_image_zero_finiteOrder` at each stratum point. Exact rank implies rank at most r, so image monotonicity restricts the resulting null rank-upper neighborhood to the exact stratum. `SardFiniteOrderRankLocusLocalAggregationProbe.measure_image_zero_of_rankLocus_pointwise_open` aggregates these local images using second countability. No measurability of the stratum or continuity of a neighborhood selection is assumed.

The older arbitrary-measurable-target induction predicate is neither assumed nor derived. Lower-dimensional Borel-compatible induction and criticality of the whole stratum remain explicit; this is not full critical-image nullity.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers, not observed uptake. Critical ranks must still be combined with rank-zero nullity, Borel-compatible induction closed, and the complementary analytic range repaired before rectangular localization. The frozen consumer is unchanged.

Provenance: byte-identical promotion of `/tmp/SardBorelPositiveRankStratumNullityProbe.lean`, SHA-256 `b4adcb681a4c39338280c39060d08c3e50a759fae2d14dd7bf8f5f72665534fc`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if exact-rank containment fails to transfer rank-upper local nullity, second-countable aggregation fails under these hypotheses, or nonstandard axioms are required.
