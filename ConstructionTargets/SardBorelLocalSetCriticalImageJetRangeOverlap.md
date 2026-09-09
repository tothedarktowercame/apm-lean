# Borel local-set critical-image overlap nullity

Provides `localSet_criticalImage_zero_of_borel_jet_range_overlap_induction`.

For nontrivial finite-dimensional real inner-product Borel spaces E and F, a proper source, and an add-Haar target measure, assume pointwise ambient C^(k+2) regularity at every point of an arbitrary source set s. Classical order admissibility, Borel-compatible critical-nullity induction at every strictly lower source dimension, and the natural-number inequality

`dim E + (dim E - 1) / dim F ≤ dim F + (k + 2) + 1`

are retained. The conclusion is nullity of the image of the nonsurjective ambient derivative locus intersected with s. Neither openness nor measurability of s is required. The hypothesis is ambient `ContDiffAt`, not merely `ContDiffWithinAt`.

## Proof and observed dependencies

The direct import is `SardBorelOpenCriticalImageJetRangeOverlap`. At each critical point in s, finite-order `ContDiffAt.eventually` supplies an open neighborhood on which f has the required regularity. The declaration `open_criticalImage_zero_of_borel_jet_range_overlap_induction` makes the critical image there null. Image monotonicity restricts to s. The transitively imported `SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null` aggregates these certificates over the critical set.

## Boundary and consumers

No downstream consumer uptake or full rectangular closure is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. Arbitrary-set localization is established only under the displayed overlap and induction hypotheses. Dimension induction closure, the complementary analytic range, and remaining regularity and dimension cases are still obligations. No implication to the older arbitrary-measurable-target induction predicate is asserted. The frozen t93A04 statement and placeholder remain unchanged.

Stop only if finite-order ambient regularity fails to provide open regularity neighborhoods, the reviewed open-set theorem or local aggregation fails under these hypotheses, or nonstandard axioms are required.

## Provenance

The source is byte-identical to `/tmp/SardBorelLocalSetCriticalImageJetRangeOverlapProbe.lean`, SHA-256 `ab9591ef8aeb2e1076674615b2157f91683122f4030f98fa131a6392e9d908dd`. Statement lines 7–23 hash to `be6bd576dd245dce26f9bb9eda5b769a684559115ae7f234f3cc6c057e826b8e`. The fixture compiles without warnings, using only `propext`, `Classical.choice`, and `Quot.sound`.
