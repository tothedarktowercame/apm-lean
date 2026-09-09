# Borel positive-rank pointwise nullity

`SardBorelPositiveRankPointwiseClosedOpenNullityProbe.exists_open_rankUpper_image_zero_finiteOrder` constructs an open neighborhood U of a positive-rank critical point x such that the image of the derivative-rank-at-most-r locus intersected with U has zero target add-Haar measure.

The map is globally C^order for a positive finite order and satisfies classical admissibility. Its source and target are finite-dimensional real inner-product spaces, the source is complete and second-countable, and the target has a Borel-compatible measurable structure and add-Haar measure. Exact rank r at x, positivity of r, derivative nonsurjectivity at x, the exact source dimension d, and Borel-compatible classical nullity at all source dimensions below d remain explicit hypotheses.

The proof constructs a projected finite-order chart using `SardFiniteOrderProjectedSmoothChartTargetData`. `SardProjectedRankReducedDimensionIdentities` and `SardProjectedPositiveRankDimensionData` supply both reduced dimensions, rank bounds, and strict kernel dimension drop. `SardDerivativeRankUpperLocusClosed` supplies closedness of the rank-upper locus.

`SardProjectedChartResidualSlicesContDiffOn` supplies residual slice regularity from the constructed inverse chart. `SardRangeProjectionCoordinateDerivative` identifies the projected derivative, and `SardFiniteOrderProjectedChartLocalizedResidualSliceZero` supplies its localized residual-zero certificate. These constructed data instantiate `SardBorelDerivativeRangeOrthogonalClosedOpenChartNullityProbe.measure_image_zero_of_rangeOrthogonal_closedOpenChart_finiteOrder`. The neighborhood is the chart source. The zero-derivative certificate is used on the localized rank-upper locus, not asserted on an entire open neighborhood.

No chart or residual-slice certificate is a theorem premise. Borel-compatible lower-dimensional induction remains assumed; the older arbitrary-measurable-target induction predicate is neither assumed nor derived.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 remain prospective consumers, not observed uptake. Positive-rank strata must still be aggregated and combined with rank-zero nullity; full induction and the complementary analytic range remain unresolved before rectangular localization. The frozen consumer is unchanged.

Provenance: byte-identical promotion of `/tmp/SardBorelPositiveRankPointwiseClosedOpenNullityProbe.lean`, SHA-256 `533951c88e745dab8e7d87e7455b86e1de6adeed5c99e110800919eb6d5a8cc5`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if the reviewed projected chart construction, dimension identities, residual certificates, or Borel chart aggregator fail under these hypotheses, or nonstandard axioms are required.
