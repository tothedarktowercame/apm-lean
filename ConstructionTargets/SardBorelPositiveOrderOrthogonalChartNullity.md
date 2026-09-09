# Positive-order orthogonal chart nullity

`SardBorelPositiveOrderOrthogonalChartNullityProbe.measure_image_zero_of_rangeOrthogonal_closedOpenChart_positiveOrder` proves nullity of the image of a closed-open source intersection from orthogonal-coordinate chart data and positive-order lower-dimensional induction.

The finite-dimensional real inner-product target carries a Borel structure and an additive Haar measure. The proof installs the inherited Borel structures, local compactness, second countability, and additive Haar measures on the derivative range and its orthogonal complement. Nonsurjectivity of the supplied linear map makes that complement nontrivial.

Common-rank dimension identities and rank bounds provide admissibility for the smaller slice. The supplied nonzero natural order gives `1 ≤ order` at the call to `reducedDimension_slice_nullity_of_borel_positive_order`. The explicit-topology closed-open chart aggregator then yields nullity. This is a direct use of positive-order induction, not a conversion to the broader all-orders predicate.

## Hypotheses retained

The chart, first-coordinate identity, continuity on the closed-open intersection, slice regularity, zero residual derivatives, strict slice dimension drop, and lower-dimensional induction are explicit premises. This theorem does not construct these data or close induction.

## Verification and consumer status

The Lean module is byte-identical to `/tmp/SardBorelPositiveOrderOrthogonalChartNullityProbe.lean`, SHA-256 `fa1c10644ac2c5e72e46347b52d9bfb5a31d48c8eabbf0769ded6f9823ce8f6a`. Its axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

The intended consumer is frozen `t93A04`; proposed shared consumers are `t01A08`, `t01J04`, `t92J07`, and `t96J05`. No consumer uptake is claimed. Remaining work is to construct and aggregate positive-rank chart witnesses, integrate positive-order jet nullity into rank-zero aggregation, and resolve complementary analytic cases before rectangular closure. The frozen consumer and the all-orders predicate are unchanged.
