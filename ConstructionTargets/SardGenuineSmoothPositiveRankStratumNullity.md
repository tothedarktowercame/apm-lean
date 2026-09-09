# Genuine smooth positive-rank stratum nullity

`measure_image_zero_positive_rank_stratum` proves Haar-null image of the exact derivative rank-equal-r stratum for globally ContDiff real genuine infinity f, where 0 < r < target dimension.

Its sole nullity premise is local genuine-smooth critical-image induction for all strictly smaller finite-dimensional complete normed real sources and finite-dimensional inner-product targets with Borel additive Haar measure. Zero-dimensional sources are included; neither source nontriviality nor arbitrary-C1 induction is required. This premise applies directly to each actual orthogonal complementary target at a varying basepoint.

Finite dimensionality derives properness and second countability of the source. The existing derivative-range packages supply inherited Borel and proper-space data. Coordinate Haar measures are chosen as Measure.addHaar; their instances are proved, not assumed as chart data. Explicit Borel and Haar proof arguments resolve Lean inference at the dependent complement type.

At each stratum point the proof invokes SardGenuineSmoothOpenRankUpperImageNullity, obtaining the actual chart and null rank-upper image. The stratum rank equality supplies both the basepoint bounds and inclusion in that rank-upper set. Its actual open chart source and basepoint membership feed measure_image_zero_of_rankLocus_pointwise_open. Despite its module name, that aggregation theorem is purely topological and measure-theoretic; no finite-order Sard theorem is applied.

This is a conditional positive-rank stratum theorem. Rank-zero coverage, compatible local-domain induction discharge and base cases, full critical-set assembly and manifold transport remain. The frozen t93A04 placeholder is unchanged. No unconditional Sard result follows.
