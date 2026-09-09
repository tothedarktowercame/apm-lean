# Borel overlap nullity in normed spaces

`localSet_criticalImage_zero_of_borel_overlap_normed_spaces` proves localized
critical-image nullity for finite-dimensional real normed source and target
spaces. The target carries a Borel structure and an additive Haar measure.
The source set is arbitrary; no source measurable structure is required.

Pointwise ambient `C^(k+2)` regularity, classical order admissibility,
Borel-compatible critical nullity at every strictly smaller source dimension,
and the natural-number overlap inequality remain explicit premises. Neither
space needs an inner-product assumption, and neither source nor target models,
equivalences, or model measures are supplied by the caller.

## Construction and dependency

The proof constructs `EuclideanSpace ℝ (ULift.{v} (Fin (Module.finrank ℝ F)))`
in the target universe. Its finrank equals that of `F`.
`LinearEquiv.ofFinrankEq` and `LinearEquiv.toContinuousLinearEquiv` provide
the target equivalence; Euclidean volume supplies the model Haar measure.
The directly imported and invoked theorem
`localSet_criticalImage_zero_of_borel_overlap_target_equiv` transfers nullity
back to the original target. The source model is already internal to that
reviewed dependency chain.

## Evidence and residual

The Lean source is byte-identical to the acceptance fixture
`/tmp/SardBorelOverlapNormedSpacesProbe.lean`, SHA-256
`1db860f024e11b5ed3e4132edd2ca085b4a5166f7ee3a6ec9d688b9aa9e8527f`.
The axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Intended consumers are `t93A04`, `t01A08`, `t01J04`, `t92J07`, and `t96J05`.
No frozen consumer is closed here. Representation and supplied-model
assumptions are discharged, but Borel-compatible dimension induction,
complementary analytic ranges, and remaining regularity cases are unresolved.
The overlap inequality has not been removed. The frozen `t93A04` theorem and
its one placeholder remain unchanged.

Stop only if the same-universe Euclidean target model lacks the required
dimension or Haar structures, finite-dimensional linear equivalence fails to
be continuous, reviewed target transfer fails under these hypotheses, or
nonstandard axioms are required.
