# Lower-dimensional critical-image comparison

`criticalImage_eq_image_of_lower_dimension` identifies the localized
nonsurjective ambient `fderiv` image of an arbitrary map with its entire
subset image when source finrank is strictly smaller than target finrank.
Both spaces are finite-dimensional real normed spaces.

The comparison runs as exact equality from
`f '' (s ∩ {x | ¬ Function.Surjective (fderiv ℝ f x)})` to `f '' s`.
No differentiability, continuity, measurable structure, or measure is assumed.
Every `fderiv` value is a continuous linear map even when it is not a
derivative witness. Surjectivity would force its range finrank to equal
target finrank, contradicting the bound by source finrank. Thus the
nonsurjectivity locus contains every point and intersection with it leaves
`s` unchanged.

The observed import is `SardLowerDimensionAmbientImageNullity`; the proof
uses finite-dimensional linear algebra directly, not that module's nullity
theorem. This equality itself asserts no nullity. In particular, it exposes
the order-zero induction obligation as entire-image nullity under C0
regularity; it neither proves that obligation nor supplies a counterexample.

The Lean source matches `/tmp/SardLowerDimensionCriticalImageEqualityProbe.lean`,
SHA-256 `16fe2a309f9654f2469b526d68ed6c102e3088d91b646611a1cd7eed631fd620`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Intended consumers are t93A04 and the shared Sard foundation for t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is closed here. The next task
is auditing the order-zero induction specification while preserving the
smooth frozen consumer; complementary higher-order analytic cases also
remain. The ledger and frozen consumer are unchanged.

The boundary would be a surjective linear map from strictly smaller finite
dimension, failure of the stated image equality, or a need for nonstandard
axioms.
