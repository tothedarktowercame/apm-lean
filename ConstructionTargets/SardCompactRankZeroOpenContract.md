# Compact rank-zero nullity with open-domain induction

The public compact theorem concerns a globally ContDiff real infinity map
from a nontrivial finite-dimensional complete real inner-product space E to
a nontrivial finite-dimensional real inner-product space F with Borel Haar
measure. K is compact and fderiv f vanishes on K. Source Borel structure and
properness are derived locally. Nontriviality is required only for the ambient
E and F; the induction premise includes zero-dimensional smaller sources.

`SardOpenContractFirstJetProbe.exists_local_firstNonzeroJet_image_null`
uses the existing scalarized genuine-smooth jet chart and kernel dimension
drop. Its actual parameter domain U is `{z | (0,z) ∈ e.target}`, proved open.
The inverse slice g and f composed with g are ContDiffOn infinity on U.
The sole local induction premise is critical-image nullity for smooth maps
on explicitly open domains in the smaller kernel source. It applies to the
composite on U. Existing parameterized critical-image transport proves that
the parameter representatives of the localized jet locus are critical and
transfers nullity back. No chart, derivative identity or jet-locus nullity is
assumed; regularity comes from the constructed chart on its open domain.

`SardCompactRankZeroOpenContractProbe.compact_rankZero_image_null_of_smooth_local_induction`
uses this local result, the existing nonzero scalar-direction producer,
jet-locus aggregation, and compact admissible higher-jet/Taylor assembly.
The compact set's criticality follows from its zero derivative and the
nontrivial target. The induction premise ranges over all strictly smaller
complete finite-dimensional real inner-product sources and open smooth
domains, without a positivity restriction on their dimension.

`compact_rankZero_image_null_of_global_induction` supplies exactly that
premise through the banked open-domain localization compatibility theorem
from smaller-dimensional global smooth critical-image nullity.

Existing stronger-premise APIs are unchanged. No arbitrary-set pointwise
infinity premise, arbitrary-C1 induction or analytic omega is substituted.
This is conditional compact rank-zero nullity only. Rank-zero exhaustion,
global critical-set assembly with repaired positive-rank nullity, compatible
induction discharge, ambient degenerate cases and manifold transport remain.
