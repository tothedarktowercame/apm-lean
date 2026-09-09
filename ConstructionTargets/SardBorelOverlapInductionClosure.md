# Conditional Borel overlap induction closure

`borelClassicalCriticalNullity_of_overlap_complement` assembles strong
source-dimension induction using the reviewed normed-space overlap theorem.
This is a conditional theorem, not a proof of unconditional Morse-Sard.

## Premise and conclusion

The explicit premise `hremaining` must prove critical-image nullity for every
admissible finite order in either of these cases: `order < 2`, or
`targetDim + order + 1 < sourceDim + (sourceDim - 1) / targetDim`.
It may assume Borel-compatible classical critical nullity at every strictly
smaller source dimension. All arithmetic here is natural-number arithmetic.
This analytic premise remains unproved by this module.

Given that premise, the conclusion is
`BorelClassicalCriticalNullityAtDimension` at every dimension: finite-dimensional
real normed source and target spaces, a Borel target with additive Haar
measure, arbitrary source sets, and pointwise ambient finite-order regularity.
The broader predicate without target Borel compatibility is not claimed.

## Proof and observed dependencies

`Nat.strong_induction_on` supplies the lower-dimensional hypothesis. Low
orders use `hremaining`. For orders at least two, the overlap inequality
either holds or its strict complement holds. In the overlap branch, write
the order as `k + 2` and invoke
`localSet_criticalImage_zero_of_borel_overlap_normed_spaces`, transporting
the source dimension equality to all its premises. The complementary branch
uses `hremaining` with the strict inequality.

The direct import is `ConstructionTargets.SardBorelOverlapNormedSpaces`;
the Borel classical predicate is available through that dependency chain.

## Evidence and residual

The Lean source is byte-identical to
`/tmp/SardBorelOverlapInductionClosureProbe.lean`, SHA-256
`7e2f02676632f92731536ed6292d426a30de86f22c8c05c982a4a271db7ee59c`.
Its axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

Proposed consumers are `t93A04`, `t01A08`, `t01J04`, `t92J07`, and `t96J05`;
no frozen consumer is closed by this increment. Prove the explicit low-order
and complementary-overlap inductive premise next, then specialize the result
to the remaining rectangular and manifold interfaces. The frozen `t93A04`
statement and its one placeholder are unchanged.

Stop only if the order and overlap split is not exhaustive, strong induction
cannot instantiate the reviewed overlap theorem under these hypotheses, or
nonstandard axioms are required.
