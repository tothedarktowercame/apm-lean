# Compact rank-zero assembly with uncovered orders starting at three

`compact_rankZero_image_zero_of_uncovered_third_and_higherJets` proves zero target add-Haar measure of the image of a compact rank-zero source set K.

The theorem retains global C^(k+2) regularity, classical Sard admissibility, and full classical nullity at strictly lower source dimensions. Explicit jet-image nullity is required only for 3 <= j <= k+2 with j * targetDim <= sourceDim - 1. The nontrivial finite-dimensional real inner-product, Borel, and proper-source assumptions are exactly those in the Lean declaration.

The proof invokes the reviewed compact uncovered-jet assembly and splits off order two. Rank zero implies criticality because a surjective derivative would have full target rank, contradicting target nontriviality. The second-jet classical induction theorem then supplies order-two nullity. All remaining uncovered orders satisfy j >= 3; strict-surplus orders are handled by the underlying assembly.

Observed dependencies are `SardCompactRankZeroUncoveredJetAssembly` and `SardSecondJetClassicalInductionNullity`. The intended consumer is t93A04; proposed additional consumers are t01A08, t01J04, t92J07, and t96J05. No consumer is modified or closed by this module.

The residual is to discharge uncovered orders j >= 3, close full lower-dimensional induction, and complete rank-zero exhaustion and rectangular localization. This theorem does not supply the full induction hypothesis or establish rectangular Morse–Sard. The stop boundary is failure of rank-zero criticality for the stated nontrivial target, failure of the reviewed second-jet theorem to discharge order two, or a need for nonstandard axioms.

The source is promoted byte-for-byte from `/tmp/SardCompactRankZeroThirdJetAssemblyProbe.lean`, SHA-256 `b18cbb50370860e4eee3e58f428daa9fe47480bbd20f4dac034083968496572b`. Its included axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
