# Open regularity to a global smooth germ

The declaration `exists_global_contDiff_germ_of_contDiffOn_open` constructs a globally C^n map agreeing with a given map near a specified point where the map is C^n on an open neighborhood. The order is `n : ℕ∞`, including infinite smoothness.

The source is a real inner-product space and the target a real normed space. Neither finite-dimensionality nor completeness is assumed. The conclusion is eventual equality at the point, not equality on the entire supplied open set.

Choose a ball of radius r contained in the open neighborhood, then a smooth bump with inner radius r/4 and outer radius r/2. Multiplying the original map by the bump gives the extension. On the closed outer ball, regularity follows from the original open-local hypothesis and the smooth scalar multiplication rule. Outside it the product is locally zero. Near the center the bump equals one, giving the asserted germ equality. No compact-support conclusion is asserted in infinite-dimensional spaces.

The direct dependencies are Mathlib's inner-product bump functions and differentiability operations. The reviewed critical-image jet-range overlap row is a scheduling dependency identifying the intended localization use, not an import or an assumption of this proof.

The intended consumer is t93A04; t01A08, t01J04, t92J07, and t96J05 are prospective consumers. No problem-facing uptake is claimed. Next, transfer local critical images through the constructed germs and aggregate neighborhoods. Full lower-dimensional induction and the complementary regularity range remain unresolved.

Provenance: byte-identical promotion of `/tmp/SardOpenRegularityGlobalGermExtensionProbe.lean`, SHA-256 `622730360f86ab1ae0064f2dde42ce48c74b67532f15bc7e5b417c92bd944197`. The axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.

Stop only if the smooth bump construction fails to preserve global regularity or local equality under the stated hypotheses, or nonstandard axioms are required.
