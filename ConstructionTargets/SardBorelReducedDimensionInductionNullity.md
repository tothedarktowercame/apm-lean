# Borel reduced-dimension induction nullity

`SardBorelReducedDimensionInductionNullityProbe.reducedDimension_slice_nullity` supplies localized critical-image nullity for maps between reduced-dimensional real normed spaces G and S. It assumes Borel-compatible classical nullity at every source dimension below d, `finrank G < d`, and dimension identities `finrank G = sourceDim - rank` and `finrank S = targetDim - rank`.

Classical admissibility is supplied at the original source and target dimensions, with rank bounded by both. The target S has an explicit Borel-compatible measurable structure and add-Haar measure. The conclusion applies to every map q and arbitrary source subset u with ambient pointwise regularity `ContDiffAt` of the unchanged finite order. Its image is restricted to points of u where the derivative is nonsurjective.

The direct imports and observed uses are `SardRankDropRegularityAdmissibilityProbe.sardOrderAdmissible_sub_rank` and `SardBorelClassicalCriticalNullityPredicateProbe.BorelClassicalCriticalNullityAtDimension`. Common rank subtraction preserves admissibility; the dimension identities then instantiate the lower-dimensional Borel-compatible predicate. Both rank bounds are retained to control natural-number subtraction.

The older arbitrary-measurable-target predicate is neither assumed nor derived. The lower-dimensional Borel-compatible predicate remains an induction premise; this packet does not close induction or construct analytic slice regularity.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers, not observed uptake. The next edge is to connect this interface to positive-rank chart assembly. Full induction and the complementary analytic range remain unresolved before rectangular localization. The frozen consumer is unchanged.

Provenance: byte-identical promotion of `/tmp/SardBorelReducedDimensionInductionNullityProbe.lean`, SHA-256 `286b31b3461b1d10426a8d6e529f28f5c1c0317fd100191d7df2492ed1f0cbdf`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if common rank subtraction fails to preserve admissibility under both rank bounds, explicit Borel compatibility fails to instantiate the induction predicate, or nonstandard axioms are required.
