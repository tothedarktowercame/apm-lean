# Borel overlap target-equivalence transfer

`localSet_criticalImage_zero_of_borel_overlap_target_equiv` proves nullity of
the localized critical image of a map between finite-dimensional real normed
spaces, using a supplied continuous linear equivalence from its target `F`
to an inner-product model `H` in the same universe.

Both targets carry Borel structures and additive Haar measures. The arbitrary
source set need not be open or measurable. Pointwise ambient `C^(k+2)`
regularity, classical order admissibility, Borel-compatible critical nullity
in every strictly lower source dimension, and the overlap inequality remain
explicit premises. There is no inner-product assumption on `F`, nor a
supplied nullity certificate for the coordinate map.

## Proof and observed dependencies

Composition with the target equivalence preserves pointwise regularity.
Its finrank equality transports admissibility and the overlap inequality.
`localSet_criticalImage_zero_of_borel_overlap_normed_source` then proves
nullity of the coordinate map's critical image with respect to the model
Haar measure. `criticalImage_eq_of_target_continuousLinearEquiv` identifies
that set with the equivalence-image of the original critical image.
`SardContinuousLinearEquivImageNullityProbe.ContinuousLinearEquiv.measure_zero_of_image_zero_addHaar`
reflects nullity back to the original target measure. No equality of the two
Haar measures is claimed. All three corresponding modules are direct imports.

## Evidence and remaining work

The Lean source is byte-identical to the acceptance fixture
`/tmp/SardBorelOverlapTargetEquivTransferProbe.lean`, SHA-256
`90976f5f662ef33f1d645fe6cf772f1aeeeda16620663665e9cea1b84bb0ab2a`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Proposed consumers are `t93A04`, `t01A08`, `t01J04`, `t92J07`, and `t96J05`.
No frozen consumer is closed by this increment. The next edge is internal
construction of the target model and its Haar measure. Borel-compatible
dimension induction, complementary analytic ranges, and remaining regularity
cases still require proof. The frozen `t93A04` statement and its one
placeholder remain unchanged.

Stop only if target-equivalence composition fails to preserve regularity or
dimension premises, reviewed critical-image equality or Haar-nullity
reflection fails under these hypotheses, or nonstandard axioms are required.
