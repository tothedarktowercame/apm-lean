# Open-localized rank-zero nullity from uncovered jets

`rankZero_inter_open_image_zero_of_uncovered_higherJets` proves zero target add-Haar measure of the image of the derivative rank-zero locus intersected with an open source set U.

The theorem assumes global C^(k+1) regularity and classical Sard order admissibility. For each order 2 <= j <= k+1 with j * targetDim <= sourceDim - 1, it retains nullity of the first-nonzero-j-jet image on U as an explicit hypothesis. The nontrivial finite-dimensional real inner-product, Borel, and proper-source assumptions are exactly those in the Lean declaration. There is no compactness assumption on U and no small-source dimension restriction.

The proof derives C1 regularity and closedness of the rank-zero locus, then uses closed-open compact exhaustion. For each compact member, containment in U transfers the uncovered jet-image nullity by measure monotonicity. The reviewed compact assembly discharges the complementary strict-surplus orders internally.

Observed dependencies are `SardCompactRankZeroUncoveredJetAssembly`, `SardClosedOpenImageNullity`, and `SardDerivativeRankUpperLocusClosed`. The intended consumer is t93A04; proposed additional consumers are t01A08, t01J04, t92J07, and t96J05. No frozen consumer is changed or closed by this module.

The remaining work is to prove the uncovered higher-jet nullity hypotheses, close full lower-dimensional induction, and remove global regularity through rectangular localization. This is conditional rank-zero assembly, not a complete rectangular Morse–Sard theorem. The stop boundary is failure of closedness, exhaustion, or jet containment under the stated hypotheses, or a need for nonstandard axioms.

The source is promoted byte-for-byte from `/tmp/SardRankZeroOpenUncoveredJetNullityProbe.lean`, SHA-256 `dfd5d0b5530304a0d52648971e948aad757fe24c2b3bd18f0c249175a6a93c06`. The included axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
