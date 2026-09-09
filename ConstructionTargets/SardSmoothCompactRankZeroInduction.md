# Compact rank-zero nullity from local smooth induction

2026-09-09, codex-12; read-only probe.

The complete theorem
SardSmoothCompactRankZeroInductionProbe.compact_rankZero_image_null_of_smooth_local_induction
proves Haar-null image of a compact K for globally genuinely smooth f, given
fderiv(f,y)=0 for y in K and a local smooth critical-image induction hypothesis
for every strictly smaller finite-dimensional real normed source.

The induction hypothesis includes complete zero-dimensional sources: there
is no Nontrivial requirement on G. The source E and target F of the conclusion
are nontrivial finite-dimensional real inner-product spaces. Target measure
is an actual IsAddHaarMeasure; standard Borel and proper-source instances are
explicit. The only nullity premise is the declared lower-dimensional local
smooth induction, not higher-jet nullity or the desired rank-zero conclusion.

The proof first derives criticality on K from fderiv=0 and nontrivial F.
For each first-nonzero jet of order j>=2, it writes j=i+1 with i>=1 and
uses SardNonzeroSuccessorJetScalarDirections to select actual h, directions,
and scalar functional from that nonzero jet. The exact derivative kernel
supplies the smaller-source induction instance. The reviewed
SardSmoothFirstNonzeroJetLocalInduction theorem constructs an open chart
containing the locus point with null local image. Its source/open-source
fields feed SardFirstNonzeroJetLocusLocalAggregation, yielding null image
of the entire higher-jet locus.

Take k=finrank(E), so the finite differentiability order is k+1. Genuine
infinity smoothness supplies that finite order. The existing admissibility
inequality finrank(E)<finrank(F)+(k+1) is proved arithmetically. These derived
higher-jet facts feed compact_rankZero_image_zero_of_admissible_higherJets,
which handles finite-jet decomposition, the empty first-jet stratum and
flat-locus Taylor nullity. First derivative zero is never used to infer
higher-order flatness.

Validation: lake env lean /tmp/SardSmoothCompactRankZeroInduction.lean exits 0,
without warnings. Axioms are propext, Classical.choice and Quot.sound; no
placeholders. No existing module imports the new local-induction producer at
this probe. Frozen t93A04 remains unchanged with one executable placeholder.

Prospective scope: ConstructionTargets/SardSmoothCompactRankZeroInduction.lean
and ConstructionTargets/SardSmoothCompactRankZeroInduction.md.

This is a conditional compact rank-zero induction step. Positive-rank reduction
with preserved smoothness, compatible local-domain induction, base cases,
full critical-set coverage and manifold transport remain before unconditional
Sard or frozen t93A04 closure. No ledger or canonical source changes were made.
