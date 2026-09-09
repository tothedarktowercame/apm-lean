# Positive-order critical-rank aggregation

This module assembles positive-rank critical images using positive-order Borel induction. Both declarations are in `SardBorelPositiveOrderRankAggregationProbe`.

`measure_image_zero_of_positive_rankStratum_positiveOrder` obtains local rank-upper nullity from the reviewed pointwise theorem, restricts it to the exact-rank locus, and applies local null aggregation. Criticality of the positive-rank stratum is an explicit premise.

`measure_criticalImage_zero_of_rankZero_positiveOrder` uses the bounded critical-rank decomposition. Rank zero is handled by the supplied rank-zero image-nullity premise. For each positive rank below the target dimension, surjectivity would force full target rank, giving a contradiction; the first theorem then supplies that stratum's nullity.

The spaces are finite-dimensional real inner-product spaces, with a Borel target carrying an additive Haar measure. Global regularity at a nonzero admissible finite order and positive-order critical nullity below the source dimension remain explicit hypotheses. No conversion to the broader all-orders predicate is used.

## Verification and remaining work

The module reproduces `/tmp/SardBorelPositiveOrderRankAggregationProbe.lean`, SHA-256 `2da77fc50e6060495cfb39452974c4664bf7c194c16ced4973df2ac0e1b48b78`. Both axiom audits use only `propext`, `Classical.choice`, and `Quot.sound`.

The intended frozen consumer is `t93A04`; proposed shared consumers are `t01A08`, `t01J04`, `t92J07`, and `t96J05`. No consumer uptake is claimed. Prove rank-zero nullity using positive-order jet aggregation, resolve complementary analytic cases, close induction, and localize before rectangular closure. This module does not discharge its rank-zero premise, prove the induction hypothesis, or alter the frozen consumer.
