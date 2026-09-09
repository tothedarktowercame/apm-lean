# Borel-compatible classical critical-nullity predicate

The namespace `SardBorelClassicalCriticalNullityPredicateProbe` provides `BorelClassicalCriticalNullityAtDimension` and proves `borelClassicalCriticalNullity_zero`.

The predicate quantifies over finite-dimensional real normed sources of exact finrank d, finite-dimensional real normed targets with Borel-compatible measurable structures, and target add-Haar measures. It retains every natural regularity order satisfying classical Sard admissibility, arbitrary source subsets, ambient pointwise ContDiffAt regularity, and the localized nonsurjective-derivative image conclusion.

The base theorem instantiates the reviewed zero-dimensional Borel critical-image theorem. Its proof needs neither regularity nor admissibility beyond the parameters retained by the predicate, and handles trivial targets through that dependency.

This is a distinct proposition from `ClassicalCriticalNullityAtDimension`: the latter quantifies over arbitrary measurable target structures without the Borel premise. The existing predicate and every existing analytic declaration remain unchanged. No equivalence or reverse implication between predicates is asserted. The new predicate cannot simply be substituted for the old hypothesis in already banked conditional theorems.

The direct import and observed proof dependency is `SardZeroDimensionalBorelCriticalImage`, specifically `criticalImage_zero_of_source_finrank_zero_borel`. The earlier classical predicate supplies the scheduling and transitive admissibility context. The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers, not claimed uptake.

Next, reprove the required analytic induction interfaces using this explicit Borel-compatible predicate, close positive-dimensional induction, and repair the complementary regularity range before rectangular closure. The frozen consumer is unchanged.

Provenance: byte-identical promotion of `/tmp/SardBorelClassicalCriticalNullityPredicateProbe.lean`, SHA-256 `ab52aa42ad6df9f3fe87359b106ff68318782df89fdd1046ac1e8eb7401669c3`. The base theorem's axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if the zero-dimensional theorem fails to instantiate this predicate, its quantifiers fail to preserve the stated localized classical conclusion, or nonstandard axioms are required.
