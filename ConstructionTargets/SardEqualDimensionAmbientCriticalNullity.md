# Equal-dimensional ambient critical-image nullity

`equalDimension_ambient_criticalImage_zero` proves localized critical-image
nullity between finite-dimensional real normed spaces of equal finrank.
The target carries a Borel structure and an additive Haar measure. The map
is ambient differentiable at every point of an arbitrary source subset.

No source measurable structure or Haar measure is assumed. Neither a supplied
equivalence nor derivative continuity, openness, measurability of the subset,
or unique differentiability of the subset is required.

## Construction and observed dependencies

`LinearEquiv.ofFinrankEq` and `LinearEquiv.toContinuousLinearEquiv` construct
a continuous linear equivalence `e : F ≃L[ℝ] E`. Composition gives a self-map
`f ∘ e` of the target space, differentiable on `e ⁻¹' s`.
The directly imported `sameSpace_ambient_criticalImage_zero` proves its
critical image null with respect to the original target measure.
The directly imported `criticalImage_eq_of_source_continuousLinearEquiv`
identifies this set exactly with the original localized critical image.
No measure transport is needed because the target remains `F` throughout.

## Evidence and residual

The Lean source is byte-identical to the acceptance fixture
`/tmp/SardEqualDimensionAmbientCriticalNullityProbe.lean`, SHA-256
`dbb3ca05674292fa6426ee6bd697c0816f63629f4f7164e8b3648e58767b09ca`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Proposed consumers are `t93A04`, `t01A08`, `t01J04`, `t92J07`, and `t96J05`.
No frozen consumer is closed here. Equal-dimensional ambient critical nullity
is established; lower-source-dimensional low-order cases and the
complementary-overlap analytic premise remain unresolved. The frozen
`t93A04` statement and its one placeholder are unchanged.

Stop only if equal finrank fails to provide a continuous linear equivalence,
differentiability fails to transport through it, reviewed source critical-image
equality or same-space nullity fails under these hypotheses, or nonstandard
axioms are required.
