# Critical-image equality under source coordinates

Provides `criticalImage_eq_of_source_continuousLinearEquiv` for real normed spaces E, G, and F, a continuous linear equivalence `e : G ≃L[ℝ] E`, a map `f : E → F`, and an arbitrary set s. The only regularity premise is differentiability of f at every point of s.

## Representation comparison

Source: the image under f of its ambient derivative-critical locus intersected with s.

Target: the image under `f ∘ e` of its ambient derivative-critical locus intersected with `e ⁻¹' s`.

Direction: exact equality from the target coordinate-composite critical-image representation to the source original-map critical-image representation, as subsets of the unchanged real normed target F. This is set equality, not just nullity transfer or inclusion.

## Proof and dependencies

The direct import is the reviewed `SardCriticalSetUnderParameterization` module. The proof uses the available chain-rule declarations `HasFDerivAt.comp`, `ContinuousLinearEquiv.hasFDerivAt`, and `HasFDerivAt.fderiv` directly; it does not call the imported module's named parameterization theorems. Composition of the derivative with e is surjective exactly when the original derivative is surjective, using e and its inverse to transport witnesses. This yields pointwise equivalence of criticality on the preimage of s. The two image inclusions use e and its inverse, respectively.

No finite-dimensionality, inner-product structure, measure, measurability, or global regularity is assumed. The differentiability hypothesis is essential to the chain-rule argument and is not weakened to a claim about arbitrary totalized derivatives.

## Consumer residual

No downstream uptake or full rectangular closure is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. Use this equality with regularity and dimension transport to bridge normed and inner-product source representations. Target representation, Borel-compatible induction closure, complementary analytic ranges, and remaining regularity cases remain open. The frozen t93A04 statement and placeholder are unchanged.

Stop only if the chain rule and invertible source derivative fail to preserve criticality in both directions, inverse coordinates fail to identify the localized images, or nonstandard axioms are required.

## Provenance

The source is byte-identical to `/tmp/SardSourceEquivCriticalImageProbe.lean`, SHA-256 `732285f5cec6582ac1fd7d74784474cf041bcedfb0e00ce4680c25d39122db8c`. Statement lines 5–13 hash to `a986fcda545db6887221027e6d073f24428b909d107bde27c424b8437d571cf8`. The fixture compiles without warnings using only `propext`, `Classical.choice`, and `Quot.sound`.
