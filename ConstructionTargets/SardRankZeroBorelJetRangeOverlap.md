# Rank-zero Borel jet-range overlap

`rankZero_image_zero_of_borel_jet_range_overlap_induction` proves zero target add-Haar measure of the image of the entire derivative rank-zero locus. No compactness or jet-nullity premise is supplied.

The theorem retains global C^(k+2) regularity, classical admissibility, Borel-compatible classical critical-image nullity at every strictly lower source dimension, and the bound `sourceDim + floor((sourceDim - 1) / targetDim) <= targetDim + k + 3`. Source and target are nontrivial finite-dimensional real inner-product spaces with Borel-compatible measurable structures; the source is proper.

The three direct imports discharge distinct steps. `SardDerivativeRankUpperLocusClosedProbe.isClosed_derivativeRankAtMost` supplies closedness after restricting regularity to C1 and identifying rank at most zero with rank zero. `SardClosedOpenImageNullityProbe.measure_image_zero_of_closed_inter_open` exhausts this closed locus, using the whole source as its open neighborhood. Each compact subset is handled by `compact_rankZero_image_zero_of_borel_jet_range_overlap` from `SardCompactRankZeroBorelJetRangeOverlap`. Simplification removes intersection with the whole source.

The older arbitrary-measurable-target induction predicate is neither assumed nor derived. The Borel-compatible induction premise and overlap restriction remain explicit; this theorem does not prove full critical-image nullity.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 remain prospective consumers, not observed uptake. Positive-rank assembly still needs Borel-compatible induction interfaces, induction needs closure, the complementary analytic range needs repair, and global regularity needs removal through localization. The frozen consumer is unchanged.

Provenance: byte-identical promotion of `/tmp/SardRankZeroBorelJetRangeOverlapProbe.lean`, SHA-256 `0422ca8e6857e86f2fbe87d820c08991e26e6aab0cf12a407244a03c14f1d956`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if C1 rank-zero closedness or compact exhaustion fails to transfer the reviewed compact overlap nullity under these hypotheses, or nonstandard axioms are required.
