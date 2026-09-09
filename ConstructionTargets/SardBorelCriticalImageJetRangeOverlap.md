# Borel critical-image nullity in the jet-range overlap regime

Provides `criticalImage_zero_of_borel_jet_range_overlap_induction`.

For nontrivial finite-dimensional real inner-product Borel spaces E and F, a proper source E, and an add-Haar target measure, assume global C^(k+2) regularity, classical order admissibility, Borel-compatible critical-nullity induction at every strictly lower source dimension, and

`dim E + (dim E - 1) / dim F ≤ dim F + (k + 2) + 1`.

The quotient is natural-number division. The conclusion is zero target measure of the image of the nonsurjective-derivative locus intersected with any source subset s. No measurability of s is required.

## Proof and observed dependencies

`rankZero_image_zero_of_borel_jet_range_overlap_induction`, imported from `SardRankZeroBorelJetRangeOverlap`, discharges rank-zero nullity. The imported `SardBorelCriticalImageOfRankZeroNullityProbe.measure_criticalImage_zero_of_rankZero_finiteOrder` then combines it with positive-rank nullity using the same Borel-compatible induction premise. Image monotonicity restricts the entire critical image to s.

This construction supplies no external rank-zero, positive-rank, or jet-nullity certificates. It retains the overlap bound, global regularity, and lower-dimensional induction as explicit hypotheses. It does not close induction or imply the older arbitrary-measurable-target predicate.

## Consumer residual and stop condition

No downstream uptake or consumer closure is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. The remaining obligations are localization to remove global regularity, Borel-compatible induction closure, and the complementary analytic range before rectangular closure. The frozen t93A04 statement and its placeholder are unchanged.

Stop only if the reviewed Borel rank-zero overlap theorem fails to supply the critical-rank assembly premise under these hypotheses, image restriction fails, or nonstandard axioms are required.

## Provenance

The source is byte-identical to `/tmp/SardBorelCriticalImageJetRangeOverlapProbe.lean`, SHA-256 `b105d1cdcfbcd3fa67748858aa0391ca7ea302df2c81c281e7943c16877c9437`. Statement lines 7–23 hash to `3eaaea64419873e9a53b6e50d60a82de7abc08ae9ece02d14596d3ab5ada3e8a`. The fixture compiles without warnings using only `propext`, `Classical.choice`, and `Quot.sound`.
