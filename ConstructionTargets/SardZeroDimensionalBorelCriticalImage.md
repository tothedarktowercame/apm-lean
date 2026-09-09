# Zero-dimensional Borel critical image

The declaration `criticalImage_zero_of_source_finrank_zero_borel` proves zero target add-Haar measure of the localized nonsurjective-derivative image when the finite-dimensional real normed source has finrank zero.

The target is a finite-dimensional real normed space with a Borel-compatible measurable structure and an add-Haar measure. The map and source subset are arbitrary. No regularity, admissibility, nontriviality, or induction premise is assumed.

The proof splits on target subsingletonness. A subsingleton target makes every derivative surjective, so the critical set is empty. For a nontrivial target, source finrank zero implies every source point is zero. The image is therefore contained in the singleton containing f(0), and Borel-compatible Haar singleton nullity supplies the result by measure monotonicity.

The direct import is `SardClassicalFiniteOrderCriticalNullityPredicate`, providing the induction context and transitive Mathlib dependencies. The proof uses `finrank_zero_iff_forall_zero`, `measure_singleton`, and `measure_mono_null`; it does not use or establish the full classical induction predicate.

In particular, the existing predicate quantifies over arbitrary measurable target structures without a Borel compatibility premise. This theorem retains that premise explicitly and does not silently modify or discharge the broader predicate. Resolving that interface, closing positive-dimensional induction, and repairing the complementary regularity range remain necessary before rectangular closure.

The intended consumer is t93A04. The proposed additional consumers are t01A08, t01J04, t92J07, and t96J05; none is claimed as observed uptake of this new theorem. The frozen consumer is unchanged.

Provenance: byte-identical promotion of `/tmp/SardZeroDimensionalBorelCriticalImageProbe.lean`, SHA-256 `f0ff7b56bc36f9eb2f23cb1491e5b04dde2872d5716aa02f8ecb18f0d1a5007e`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if the zero-dimensional singleton reduction, subsingleton-target derivative surjectivity, or Borel-compatible Haar singleton nullity fails under the stated hypotheses, or nonstandard axioms are required.
