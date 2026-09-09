# Compact rank-zero Borel double-uncovered assembly

`compact_rankZero_image_zero_of_borel_double_uncovered_jets` proves zero target add-Haar measure of `f(K)` for a compact rank-zero set K. It assumes global C^(k+2) regularity, classical admissibility, and Borel-compatible classical critical-image nullity at every strictly lower source dimension. The source and target are nontrivial finite-dimensional real inner-product spaces with Borel-compatible measurable structures; the source is proper.

The remaining jet-nullity premise concerns only orders `3 <= j <= k+2` satisfying both `j * targetDim <= sourceDim - 1` and `targetDim + k + 2 < sourceDim + (j - 1)`. These orders are outside both the Taylor-surplus range and the admissible-loss induction range.

The proof directly invokes `compact_rankZero_image_zero_of_uncovered_higherJets` from `SardCompactRankZeroUncoveredJetAssembly`. For orders within the regularity budget, rank-zero membership and target nontriviality imply derivative nonsurjectivity, and `firstNonzeroJet_image_null_of_borel_classical_admissible_loss` from `SardJetBorelClassicalAdmissibleLossNullity` supplies nullity. Classical admissibility ensures order two is within that budget. All remaining orders use the explicit double-uncovered premise.

This is a direct Borel-compatible induction assembly. It neither assumes nor derives the older arbitrary-measurable-target induction predicate and does not change existing declarations.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers, not observed uptake. Positive-rank interfaces still need migration to Borel-compatible induction, double-uncovered jet orders need analytic nullity proofs, and induction must be closed before unrestricted rectangular localization. The frozen consumer remains unchanged.

Provenance: byte-identical promotion of `/tmp/SardCompactRankZeroBorelDoubleUncoveredAssemblyProbe.lean`, SHA-256 `0a859fa12611cb556ef08410806fe5017acc82e32cf04347bd7ab9699458b5ae`. The theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if classical admissibility fails to cover order two, the reviewed Borel jet theorem fails to instantiate covered orders, compact rank-zero aggregation fails under the stated hypotheses, or nonstandard axioms are required.
