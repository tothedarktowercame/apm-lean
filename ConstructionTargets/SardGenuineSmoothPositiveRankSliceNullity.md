# Smooth positive-rank complementary slice nullity — 2026-09-09

The probe compiles the actual chart-to-local-induction composition with genuine
infinity smoothness. Positive basepoint rank gives a strict kernel source
dimension drop using projected_positiveRank_dimension_data. Rank strictly below
target dimension gives a nontrivial orthogonal-complement target through the
orthogonal finrank sum. Neither fact is assumed separately.

The chart is produced by exists_rank_upper_residual_zero. Its basepoint,
first-coordinate identity and forward/inverse smoothness are retained. For a
fixed first coordinate, the subset consists exactly of chart-target points
whose inverse points have derivative rank at most the basepoint rank. The
produced zero residual derivative is nonsurjective because the complementary
target is nontrivial. Residual genuine-infinity regularity supplies the local
smooth induction hypothesis, and critical-set intersection equals this subset.

The sole nullity premise quantifies over every strictly smaller finite-dimensional
complete normed real source, including zero-dimensional sources, and every map
smooth at the points of its local subset. The conclusion is Haar-null image
under the actual complementary residual. No chart, dimension drop, inverse
regularity, residual nullity or arbitrary-C1 induction is assumed.

This is conditional complementary slice-image nullity, not unconditional Sard.
Product/fiber measure assembly, full rank-stratum coverage, compatible induction
discharge and manifold transport remain. Frozen t93A04 retains one placeholder.

Promotion scope is exactly ConstructionTargets/SardGenuineSmoothPositiveRankSliceNullity.lean
and its matching .md. Verify the fixture and producer hashes recorded in the
probe audit, compile the fixture and promoted module, build the promoted module,
check standard axioms and zero executable placeholders, compare the unchanged
consumer hash, and run git diff --check. Commit only these two files. Do not edit
the DAG, ledger or existing producers.
