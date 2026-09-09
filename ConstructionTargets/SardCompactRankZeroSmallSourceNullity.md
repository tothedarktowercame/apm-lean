# Compact rank-zero small-source nullity

Provides `compact_rankZero_image_zero_of_sourceDim_le_twice_targetDim`.
The module is byte-identical to the accepted fixture, SHA-256
`880a420c9f02e1911511e7c572a0a70f05f14da773efb552e11fa25b1f12e719`.

## Statement and proof

A compact rank-zero source set K has null image under a globally C^(k+1)
map satisfying classical Sard admissibility and sourceDim <= 2*targetDim.
Source and target are nontrivial finite-dimensional real inner-product Borel
spaces; the source is proper, and the target has the specified add-Haar measure.
There are no higher-jet nullity premises.

The reviewed uncovered-jet assembly reduces the claim to orders j >= 2 with
j*targetDim <= sourceDim-1. Multiplication preserves the lower bound j>=2,
so j*targetDim >= 2*targetDim >= sourceDim. Nontriviality of the source gives
positive source dimension, making this incompatible with the uncovered bound.
Thus every remaining obligation is discharged. The proof preserves classical
admissibility, compactness, and the rank-zero condition; it does not infer them
from the dimension inequality.

Observed dependency: `SardCompactRankZeroUncoveredJetAssembly`.
Expected axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Consumer boundary and verification

Intended consumer: t93A04. Other proposed consumers: t01A08, t01J04, t92J07,
t96J05. No frozen consumer is changed or closed by this packet. Localize and
exhaust this compact result in its dimension range. For sourceDim > 2*targetDim,
uncovered higher jets still require analytic repair before full rectangular
induction. This is not full rectangular Morse-Sard.

Verify fixture identity, direct compilation, focused build, axiom report,
worklist validity, and frozen-consumer invariance. Stop only if the dimension
bound fails to eliminate uncovered orders under source nontriviality, the
reviewed compact assembly fails with those obligations discharged, or
nonstandard axioms are required.
