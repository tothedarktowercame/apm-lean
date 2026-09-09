# Borel overlap nullity through a source equivalence

Provides `localSet_criticalImage_zero_of_borel_overlap_source_equiv`.

The original source E is a finite-dimensional real normed space. A same-universe finite-dimensional real inner-product model G is supplied with Borel measurable structure, properness, and a continuous linear equivalence `e : G ≃L[ℝ] E`. The target F remains finite-dimensional real inner-product and Borel, with an add-Haar measure. Assume ambient C^(k+2) regularity at every point of an arbitrary set s, classical order admissibility, Borel-compatible critical-nullity induction below finrank E, and the natural-number overlap inequality

`dim E + (dim E - 1) / dim F ≤ dim F + (k + 2) + 1`.

The conclusion is nullity of the localized critical image of f on s. E itself requires no inner-product, measurable-space, or proper-space instance. Nullity of the model map is proved, not supplied.

## Observed dependencies and proof

The direct imports are `SardSourceEquivCriticalImage` and `SardBorelOverlapDegenerateDimensions`. The equivalence preserves finrank, transporting admissibility, the induction bound, and overlap to G. Composition with e transports pointwise regularity to the preimage of s. `localSet_criticalImage_zero_of_borel_overlap_all_dimensions` proves model-map nullity. The equality `criticalImage_eq_of_source_continuousLinearEquiv` then rewrites that image to the original critical image; its differentiability premise follows from C^(k+2) regularity.

## Consumer boundary

No downstream uptake or full rectangular closure is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. Construction of a same-universe inner-product source model is still required. Target representation, Borel-compatible induction closure, complementary analytic ranges, and remaining regularity cases are unresolved. The supplied equivalence is not asserted to exist by this theorem, and no implication to the older arbitrary-measurable-target predicate is claimed. The frozen t93A04 statement and placeholder remain unchanged.

Stop only if source-equivalence composition fails to preserve regularity or dimension data, reviewed critical-image equality fails to transfer nullity, or nonstandard axioms are required.

## Provenance

The Lean source is byte-identical to `/tmp/SardBorelOverlapSourceEquivTransferProbe.lean`, SHA-256 `17a98a6872958c65643bdcdf5fe515cf26d08cfe1cfc4837325e08655ce02e4d`. Statement lines 7–23 hash to `2e061dc64563fbc1cf9bf8f04200f193631a00b6725427fc3dd4e94d6cc9d2f7`. The fixture compiles without warnings using only `propext`, `Classical.choice`, and `Quot.sound`.
