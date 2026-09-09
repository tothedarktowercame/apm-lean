# Open critical-image nullity under jet-range overlap

The declaration `open_criticalImage_zero_of_jet_range_overlap_induction` proves zero target add-Haar measure of the image of the nonsurjective-derivative locus restricted to an open source set U.

It assumes C^(k+2) regularity only on U, classical Sard admissibility, full classical critical-image nullity at every strictly lower source dimension, and the overlap bound
`sourceDim + (sourceDim - 1) / targetDim <= targetDim + k + 3`.
Division is natural-number division. Nontrivial finite-dimensional real inner-product source and target spaces, Borel structures, and a proper source remain explicit hypotheses. Global regularity and supplied germ-extension data are not assumed.

At each critical point in U, the smooth germ-extension theorem constructs a globally regular map g agreeing locally with f. Eventual equality also gives eventual equality of their derivatives. An open neighborhood where both equalities hold supplies containment of the restricted critical image of f in the critical image of g. The reviewed global overlap theorem and measure monotonicity give local nullity. The reviewed second-countable aggregation theorem then covers the entire critical source set.

Direct imports and uses are `criticalImage_zero_of_jet_range_overlap_induction`, `exists_global_contDiff_germ_of_contDiffOn_open`, and `SardLocalNullitySecondCountableAggregationProbe.image_null_of_locally_image_null`. These are observed dependency edges. The intended problem consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers. No frozen consumer closure is claimed.

The remaining obligations are to close full lower-dimensional induction, repair the complementary regularity range, and extend open-source localization to the required rectangular local-set interface. The overlap inequality is an additional restriction, not a consequence asserted here of classical admissibility.

Provenance: byte-identical promotion of `/tmp/SardOpenCriticalImageJetRangeOverlapProbe.lean`, SHA-256 `e4f8755a931f8849ceeb4e0cf10b2eb676903137c151b216008f01f008e4df54`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if eventual equality fails to transfer derivative criticality and image nullity on the extracted neighborhoods, countable aggregation fails under the stated hypotheses, or nonstandard axioms are required.
