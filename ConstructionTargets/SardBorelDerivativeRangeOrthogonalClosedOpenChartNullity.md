# Borel orthogonal closed-open chart nullity

`SardBorelDerivativeRangeOrthogonalClosedOpenChartNullityProbe.measure_image_zero_of_rangeOrthogonal_closedOpenChart_finiteOrder` proves zero target add-Haar measure of `f '' (A ∩ U)` from a chart into `range(L) × G` and Borel-compatible lower-dimensional induction.

The theorem retains a nonsurjective continuous linear map L, finite-dimensional real inner-product source and target, complete second-countable source, finite-dimensional real normed G, and Borel-compatible target measure. A is closed, U is open and contained in the chart source, f is continuous on their intersection, and the chart first coordinate agrees with the target orthogonal-coordinate first component. Residual slices have ambient regularity of a positive finite order and the stated zero derivative on the localized locus. Reduced-dimension identities, both rank bounds, classical admissibility, and induction below the exact source dimension are explicit premises.

The proof installs the existing range and orthogonal subtype topology certificates from `SardDerivativeRangeCoordinateTopologyPackage`, inherited Borel certificates from `SardDerivativeRangeInheritedBorelSpace`, and additive Haar measures using the imported inherited measure infrastructure. Nonsurjectivity supplies nontriviality of the orthogonal target. `SardTargetOrthogonalCoordinateEquiv` supplies the target coordinate equivalence.

`SardBorelReducedDimensionInductionNullityProbe.reducedDimension_slice_nullity` is instantiated with the inherited orthogonal Borel certificate hBS explicitly. This preserves the exact measurable representation; it does not replace the measurable structure. The resulting slice nullity feeds `SardFiniteOrderClosedOpenExplicitTopologyMeasureSpacesProbe.measure_image_zero_of_closedOpen_explicit_topology_measureSpaces`. The projection used there is the identity on the nontrivial orthogonal target, and the supplied residual regularity and derivative-zero data complete the aggregation.

The older arbitrary-measurable-target induction predicate is neither assumed nor derived. The new Borel-compatible induction premise is not discharged, and chart data are not constructed by this theorem.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers, not observed uptake. Next work must construct the required positive-rank chart data with Borel-compatible induction, aggregate rank strata, close induction, and repair the complementary analytic range before rectangular localization. The frozen consumer is unchanged.

Provenance: byte-identical promotion of `/tmp/SardBorelDerivativeRangeOrthogonalClosedOpenChartNullityProbe.lean`, SHA-256 `4bf7909f7e2b0c003e53a36ce644077e4278daea593945c7b3187991bb5a6ea6`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if inherited orthogonal Borel compatibility fails to instantiate reduced-dimension induction, the reviewed closed-open chart aggregator fails under the stated data, or nonstandard axioms are required.
