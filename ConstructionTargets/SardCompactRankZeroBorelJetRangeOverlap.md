# Compact rank-zero Borel jet-range overlap

`compact_rankZero_image_zero_of_borel_jet_range_overlap` proves zero target add-Haar measure of `f(K)` for compact rank-zero K. Its hypotheses retain global C^(k+2) regularity, classical admissibility, and Borel-compatible classical critical-image nullity at every strictly lower source dimension. The source and target are nontrivial finite-dimensional real inner-product spaces with Borel-compatible measurable structures, and the source is proper.

The explicit overlap bound is `sourceDim + floor((sourceDim - 1) / targetDim) <= targetDim + k + 3`. No jet-image nullity premise is supplied.

The direct import and observed use is `compact_rankZero_image_zero_of_borel_double_uncovered_jets` from `SardCompactRankZeroBorelDoubleUncoveredAssembly`. For a proposed double-uncovered order j, Taylor failure gives `j * targetDim <= sourceDim - 1`. Target nontriviality gives positive target dimension, so natural-number division bounds j by the quotient in the overlap hypothesis. Together with j >= 3, this contradicts admissible-loss failure. The compact assembly therefore has no remaining jet obligation in this regime.

The Borel-compatible induction hypothesis is still assumed, not proved. The older arbitrary-measurable-target predicate is neither assumed nor derived, and no equivalence with it is claimed.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers, not observed uptake. Positive-rank interfaces still need migration to Borel-compatible induction; compact nullity needs localization and exhaustion; induction needs closure; and the complementary analytic range remains unresolved. No frozen consumer is changed or closed by this packet.

Provenance: byte-identical promotion of `/tmp/SardCompactRankZeroBorelJetRangeOverlapProbe.lean`, SHA-256 `b0ef727dbcedbb2bfec03d881ea4d2876de4a4471ad7c0fd1bba1cac1d3075ed`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if the overlap inequality fails to exclude double-uncovered jet orders, the reviewed Borel compact assembly fails under these hypotheses, or nonstandard axioms are required.
