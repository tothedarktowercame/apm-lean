# Translation of test functions

This library uses the convention
`tftTranslate x ψ y = ψ (x + y)`.  Thus the `m98J02` translate is literal.
The `m98A04` function `φ (x - y)` is the translate of the reflected test
function `y ↦ φ (-y)`.

## Analytic layer

`tft_translate_bcf_continuous` (U1) says that translation of a continuous,
compactly supported function is continuous for the sup norm, i.e. as a map
into `E →ᵇ F`.  Extend the function by zero outside a compact set and use its
uniform continuity on a sufficiently large compact neighbourhood.

`tft_translate_bcf_difference_quotient` (U2) says that the directional
difference quotient converges uniformly to the translated directional
derivative.  The fundamental theorem of calculus (or the mean-value
inequality) bounds the error by the modulus of uniform continuity of
`fderiv ℝ f` on one compact neighbourhood.  The statements include the
degenerate cases `f = 0` and `v = 0`.

The relevant checked Mathlib constructions are
`BoundedContinuousFunction.ofNormedAddCommGroup`,
`HasCompactSupport.comp_homeomorph`, and `Homeomorph.addLeft`.  The small
wrapper `tftBCFOfCompactSupport` supplies the uniform bound because Mathlib's
existing `ofCompactSupport` is currently specialized to ring-valued maps.

## Fixed-support stage

`tft_local_fixed_support` (S0) constructs the compact image

`{(x,z) | ‖x-x₀‖ ≤ 1, z ∈ tsupport ψ} → E`, `(x,z) ↦ z-x`.

`tftTranslateStageLocal` bundles nearby translates in
`ContDiffMapSupportedIn E F ⊤ K`, with value zero away from the closed ball.

`tft_stage_continuousAt_of_structure_maps` (S1) reduces stage continuity to
U1 for every `iteratedFDeriv`; the universal property is
`ContDiffMapSupportedIn.continuous_iff_comp`, whose structure maps are
`ContDiffMapSupportedIn.structureMapCLM`.

`tft_stage_difference_quotient_of_structure_maps` (S2) similarly reduces
stage convergence to U2 for every iterated derivative.  An alternative direct
seminorm proof can use the checked declarations
`ContDiffMapSupportedIn.withSeminorms` and
`ContDiffMapSupportedIn.seminorm_le_iff`.

## LF layer and downstream corollaries

`tftTranslate_continuous` (T1) composes each local stage map with
`TestFunction.ofSupportedIn`; its continuity is
`TestFunction.continuous_ofSupportedIn`.  Local continuity at every base point
gives global continuity.

`tftTranslate_difference_quotient` (T2) applies the same continuous stage
inclusion to S2.  Its limit is `tftTranslate x (tftDirectional v ψ)`.

For `m98J02`, specialize `E = EuclideanSpace ℝ (Fin 2)`, `F = ℝ`, and in T2
take `v = EuclideanSpace.single i 1`.  T1 and T2 then give
`apm_m98J02_translateTest_continuous` and
`apm_m98J02_translateTest_difference_quotient` after extensional identification
of its local definitions with `tftTranslate` and `tftDirectional`.

For `m98A04`, first define the reflected test function `ρ y = φ (-y)`.
Since `tftTranslate x ρ y = φ (-(x+y))` has the wrong parameter sign, use
`tftTranslate (-x) ρ y = φ (x-y)` (equivalently precompose the parameter map
with negation).  T1 yields
`apm_m98a04_translateReflectStageLocal_continuousAt`; T2 with direction `-v`
yields its difference-quotient lemma, with the expected directional derivative
of `φ` after the two minus signs cancel.

## Parallel proof seats

Every remaining `sorry` is the complete body of a top-level lemma. Definitions,
statements, and the exported T1/T2 theorems contain no holes.

The following groups can be proved independently:

1. Direction/support infrastructure:
   `tft_directional_contDiff`, `tft_directional_hasCompactSupport`,
   `tft_local_fixed_support`, `tft_local_fixed_function_support`, and
   `tft_directional_translate_function_support`.
2. Bounded-continuous-function infrastructure and U1:
   `tft_compactSupport_bounded` and `tft_translate_bcf_continuous`.
3. U2:
   `tft_difference_quotient_continuous`,
   `tft_difference_quotient_hasCompactSupport`,
   `tft_fderiv_translate_continuous`,
   `tft_fderiv_translate_hasCompactSupport`, and
   `tft_translate_bcf_difference_quotient`.
4. Stage topology:
   `tft_stage_continuousAt_of_structure_maps` and
   `tft_stage_difference_quotient_of_structure_maps`.

After those groups, the short integration seats are
`tft_stage_continuousAt`, `tft_stage_difference_quotient`, and
`tft_stage_difference_quotient_to_lf`.  The exported
`tftTranslate_continuous` and `tftTranslate_difference_quotient` are already
assembled from these named results.
