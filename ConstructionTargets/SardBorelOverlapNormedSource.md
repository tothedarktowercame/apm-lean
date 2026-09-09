# Borel overlap nullity for normed sources

Provides `localSet_criticalImage_zero_of_borel_overlap_normed_source`.

E is an arbitrary finite-dimensional real normed space; F is a finite-dimensional real inner-product Borel space with an add-Haar measure. Assume ambient C^(k+2) regularity at every point of an arbitrary source set s, classical order admissibility, Borel-compatible critical-nullity induction below finrank E, and the natural-number overlap inequality

`dim E + (dim E - 1) / dim F ≤ dim F + (k + 2) + 1`.

The conclusion is nullity of the localized critical image. No inner-product, measurable-space, or proper-space assumptions on E, and no supplied model or equivalence, are required.

## Construction and observed dependencies

The direct imports are `SardBorelOverlapSourceEquivTransfer` and Mathlib's `Analysis.InnerProductSpace.PiL2`. The proof constructs `G := EuclideanSpace ℝ (ULift.{u} (Fin (Module.finrank ℝ E)))`. Lifting the finite index type keeps the model in the same universe as E. Standard instances supply its inner-product, finite-dimensional, Borel, and proper structures. Its finrank is computed to equal that of E. `LinearEquiv.ofFinrankEq` supplies a linear equivalence, and `toContinuousLinearEquiv` supplies continuity in finite dimensions. The reviewed `localSet_criticalImage_zero_of_borel_overlap_source_equiv` then proves the requested nullity.

## Consumer boundary

No downstream uptake or full rectangular closure is claimed. Intended consumers are t93A04, t01A08, t01J04, t92J07, and t96J05. Target representation still requires an inner-product space. Borel-compatible induction closure, the complementary analytic range, and remaining regularity cases remain open. No implication to the older arbitrary-measurable-target predicate is asserted. The frozen t93A04 statement and placeholder remain unchanged.

Stop only if the lifted Euclidean model fails to inhabit the source universe with the required dimension and structures, finite-dimensional linear equivalence fails to be continuous, reviewed transfer fails, or nonstandard axioms are required.

## Provenance

The Lean source is byte-identical to `/tmp/SardBorelOverlapNormedSourceProbe.lean`, SHA-256 `1c2e93c492c463da8931af4fb4b07a6c2f269b0672e44b894a8fd73a726ef908`. Statement lines 7–21 hash to `cbbb442846811def84a5e04e3a998859258ef8c251974297ed98aae1dd109f3d`. The fixture compiles without warnings using only `propext`, `Classical.choice`, and `Quot.sound`.
