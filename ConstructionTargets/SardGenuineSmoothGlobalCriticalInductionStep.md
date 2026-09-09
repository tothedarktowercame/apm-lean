# Global smooth critical-image induction step

`critical_image_null_of_local_smooth_induction` proves Haar-null image of the actual nonsurjective-fderiv critical set of a globally genuinely smooth map between finite-dimensional real inner-product spaces.

The sole nullity premise is local genuine-smooth critical-image induction over every strictly smaller finite-dimensional complete real normed source, including zero-dimensional sources, and finite-dimensional inner-product targets with Borel additive Haar measures. This premise is preserved; the result is not unconditional Sard.

For a subsingleton target the critical set is empty. For a subsingleton source the banked zero-dimensional critical-image result applies. Otherwise the proof installs the source Borel structure and derives properness from finite dimensionality. Continuous differentiability gives closedness of the rank-zero locus. `SardClosedOpenImageNullity` constructs an actual countable compact exhaustion using `SardClosedOpenCompactExhaustion` and aggregates null images through `SardCountableCompactImageNullity`. Each compact subset has derivative zero: zero range finrank implies bottom range and then zero continuous linear map. `SardSmoothCompactRankZeroInduction` supplies its image nullity from genuine smoothness and the given local induction hypothesis.

`criticalImage_null_of_rankStrata_null` uses the exact finite rank-stratum decomposition. The zero stratum uses the exhaustion result; each positive deficient stratum uses `SardGenuineSmoothPositiveRankStratumNullity` with the same induction hypothesis. No chart, compact coverage, stratum nullity or finite-order Sard conclusion is assumed.

The remaining consumer edge is local-domain globalization compatible with the smaller-source hypothesis, then induction discharge and actual manifold transport. Frozen t93A04 is not modified or closed.
