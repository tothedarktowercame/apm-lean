# Genuine smooth first-nonzero-jet local induction

2026-09-09, codex-12; read-only probe.

`SardSmoothFirstNonzeroJetLocalInductionProbe.exists_local_firstNonzeroJet_image_null`
constructs an open chart e whose source contains the specified locus point x,
proves containment of the first-nonzero-jet locus in its zero-coordinate
inverse slice, and proves nullity of the image of that local locus under f.
The output explicitly includes the strict kernel dimension drop and genuine
infinity smoothness of e and its inverse on their respective domains.

Inputs are globally genuinely smooth f, a critical set K, i >= 1, a point x
of firstNonzeroJetLocus f K (i+1), fixed directions and scalar functional,
and a witnessed nonzero next derivative. The sole nullity premise is a local
smooth critical-image induction hypothesis on the strictly lower-dimensional
kernel source. It quantifies over the actual maps q and local sets u with
ContDiffAt at genuine infinity at all their points. It is not an arbitrary-C1
induction hypothesis or an assumption that the desired local image is null.

The proof uses the existing actual scalarized-jet smooth chart producer.
Its forward-map equality and the existing scalarized zero-level containment
show that each locus point y in e.source satisfies (e y).1=0. Taking the
second coordinate gives a preimage in {z | (0,z) belongs to e.target}; the
chart inverse law returns y. No claim that the original unrestricted inverse
is smooth everywhere is needed. The existing scalar-derivative dimension-drop
theorem proves that this exact kernel has smaller finite dimension.

The produced smooth inverse supplies smoothness of z ↦ e.symm (0,z) through
SardProjectedChartInverseSliceContDiffOn. Together with global smoothness of f,
this feeds SardLowerDimensionalLocalCriticalImageInduction at genuine infinity.
Its reduced map is f composed with that very inverse slice. Criticality is
restricted from K using membership of the first-nonzero-jet locus in K.

The theorem is stated for an arbitrary target measure with the corresponding
induction premise; in particular it applies to Haar measure. No measure
normalization, nullity premise beyond the explicit induction hypothesis,
analytic regularity, supplied chart, or extra neighborhood regularity is used.

Validation: standalone fixture compiles without warnings or placeholders;
axioms are propext, Classical.choice and Quot.sound. Canonical source, DAG,
ledger and frozen consumer are untouched. The frozen t93A04 still has one
executable placeholder. No existing module imports the newly banked smooth
jet producer yet; this composition was not already present at this probe.

Prospective scope: ConstructionTargets/SardSmoothFirstNonzeroJetLocalInduction.lean
and ConstructionTargets/SardSmoothFirstNonzeroJetLocalInduction.md.

Remaining work: establish the induction, including base cases, other critical
rank strata, flat-locus coverage, countable/local-domain assembly and manifold
transport. This theorem is a conditional local induction step and does not
establish unconditional Sard or close t93A04.
