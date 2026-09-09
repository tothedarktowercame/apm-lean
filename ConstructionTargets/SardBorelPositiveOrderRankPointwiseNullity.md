# Positive-order positive-rank pointwise nullity

`SardBorelPositiveOrderRankPointwiseNullityProbe.exists_open_rankUpper_image_zero_positiveOrder` constructs an open neighborhood of a positive-rank critical point on which the image of the derivative-rank-at-most locus has zero additive Haar measure.

The source and target are finite-dimensional real inner-product spaces, and the target carries a Borel structure. The map is globally regular at a nonzero finite order satisfying classical dimension admissibility. Positive-order Borel critical nullity below the source dimension is an explicit induction premise.

The proof obtains a projected local chart from strict differentiability, establishes common-rank dimension identities and strict kernel dimension drop, and proves the rank-upper locus closed. It constructs slice regularity and localized residual zero-derivative certificates, then applies positive-order orthogonal chart nullity. The neighborhood is the constructed chart source; no chart or image-nullity certificates are supplied by the caller.

## Verification

The module reproduces `/tmp/SardBorelPositiveOrderRankPointwiseNullityProbe.lean`, SHA-256 `907e42910a93e8549ba708032dc71b106cc294d8b06307cc39eb57029da72d5f`. Its axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Consumer status and remaining work

The intended frozen consumer is `t93A04`; proposed shared consumers are `t01A08`, `t01J04`, `t92J07`, and `t96J05`. No consumer closure is claimed. Aggregate positive-rank neighborhoods, integrate positive-order jet nullity into rank-zero aggregation, and resolve complementary analytic cases before rectangular closure. The lower-dimensional induction premise remains unproved here, and no conversion to the broader all-orders predicate is used. The frozen consumer and existing predicates are unchanged.
