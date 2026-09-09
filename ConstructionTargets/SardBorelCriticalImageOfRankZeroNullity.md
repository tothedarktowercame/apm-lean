# Borel critical-image assembly from rank-zero nullity

Provides `SardBorelCriticalImageOfRankZeroNullityProbe.measure_criticalImage_zero_of_rankZero_finiteOrder`.

For a globally positive finite-order differentiable map between finite-dimensional real inner-product spaces, the theorem combines classical order admissibility, Borel-compatible critical-nullity induction below the exact source dimension, and an explicit null-image premise for the derivative rank-zero locus. The source is complete and second countable; the target carries a Borel-compatible add-Haar measure. The conclusion is nullity of the entire nonsurjective-derivative image.

The proof invokes `criticalImage_null_of_rankStrata_null`. Rank zero uses the supplied premise. For every positive rank below the target dimension, surjectivity would make the derivative range the whole target, contradicting its rank. The Borel-compatible positive-rank stratum theorem therefore supplies the remaining null images.

## Dependencies and boundary

Observed imports and declaration uses are the root declaration `criticalImage_null_of_rankStrata_null` from `SardCriticalRankStrataNull` and `SardBorelPositiveRankStratumNullityProbe.measure_image_zero_of_positive_rankStratum_finiteOrder` from `SardBorelPositiveRankStratumNullity`.

This is conditional infrastructure, not a closed Morse–Sard theorem. It does not discharge rank-zero nullity, close dimension induction, or identify Borel-compatible induction with the older arbitrary-measurable-target predicate. No downstream consumer uptake is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. The next obligations are rank-zero discharge, Borel-compatible induction closure, the complementary analytic range, and localization before rectangular closure. The frozen t93A04 statement and placeholder remain unchanged.

Stop only if ranks below target dimension fail to imply criticality, the reviewed Borel stratum theorem or finite rank aggregation fails under these hypotheses, or nonstandard axioms are required.

## Provenance

The Lean source is byte-identical to `/tmp/SardBorelCriticalImageOfRankZeroNullityProbe.lean`, SHA-256 `e11d2e2afb2a81882e91dd9ec26a381748de4abfc614912e011eac9facc5711c`. The statement on lines 9–22 hashes to `1decd091929d5fe4c873b4cf325490912081fba0d6bb92d07adb36a1e45d8f6e`. The fixture compiles without warnings and reports only `propext`, `Classical.choice`, and `Quot.sound`.
