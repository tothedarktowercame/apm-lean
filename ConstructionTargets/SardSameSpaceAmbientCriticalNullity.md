# Same-space ambient critical-image nullity

`sameSpace_ambient_criticalImage_zero` proves that the image of the ambient
derivative-critical locus in an arbitrary source subset has zero additive
Haar measure. The map is a self-map of a finite-dimensional real normed
Borel space and is differentiable at every point of the subset.

No rank-zero restriction, openness, measurability of the subset, unique
differentiability of the subset, derivative continuity, or nontriviality of
the space is assumed. This is a same-space theorem, not full rectangular
Morse-Sard.

## Proof and dependencies

Ambient derivative witnesses restrict to within-derivative witnesses on the
critical set. At each critical point, a nonzero determinant would give a
linear equivalence via `LinearMap.equivOfIsUnitDet`, contradicting
nonsurjectivity. The determinant is therefore zero. Mathlib's
`addHaar_image_eq_zero_of_det_fderivWithin_eq_zero` gives image nullity.
Its derivative field is the ambient derivative, not a chosen `fderivWithin`
requiring uniqueness on the subset.

The direct import is
`ConstructionTargets.SardFiniteOrderRankZeroSameSpaceEndpointNullity`.
The proof invokes the underlying Mathlib Jacobian theorem, not the imported
rank-zero theorem, and extends the application to the entire critical locus.

## Evidence and residual

The Lean source is byte-identical to the acceptance fixture
`/tmp/SardSameSpaceAmbientCriticalNullityProbe.lean`, SHA-256
`22f27c56f476e685a4f4408982b088dd5073890131502aa4df91cc70e559b126`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Proposed consumers are `t93A04`, `t01A08`, `t01J04`, `t92J07`, and `t96J05`.
No frozen consumer is closed here. Next transport to equal-dimensional
distinct spaces, handle lower-source-dimensional low-order cases, and prove
the complementary-overlap analytic premise. The frozen `t93A04` statement
and its one placeholder remain unchanged.

Stop only if ambient derivative witnesses fail to restrict to the critical
set, nonsurjectivity fails to force zero determinant in finite dimension,
the Jacobian nullity theorem fails under these hypotheses, or nonstandard
axioms are required.
