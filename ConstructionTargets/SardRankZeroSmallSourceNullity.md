# Rank-zero small-source nullity

Provides `rankZero_image_zero_of_sourceDim_le_twice_targetDim`.
The module is byte-identical to the accepted fixture, SHA-256
`fb09056b425cdfe223284b2563a3e64da279d9fb1d8d78420795f36770337dc9`.

## Statement and proof

For a globally C^(k+1) map satisfying classical Sard admissibility and
sourceDim <= 2*targetDim, the image of the entire derivative rank-zero locus
has zero target add-Haar measure. The source and target are nontrivial
finite-dimensional real inner-product Borel spaces, and the source is proper.
No compactness or higher-jet nullity premise is supplied by the caller.

Global regularity restricts to C1. The reviewed derivative-rank-upper-locus
closedness theorem at rank zero identifies a closed exact rank-zero locus,
using the equivalence of a natural number being at most zero and equal to
zero. The reviewed closed-open compact exhaustion theorem is applied with
the open set equal to the whole source. Every compact member is contained
in the rank-zero locus, so the reviewed compact small-source theorem proves
its image null. Countable exhaustion gives the stated whole-locus conclusion.

Observed dependencies: compact rank-zero small-source nullity, closed-open
image nullity, and derivative rank-upper-locus closedness. Expected axioms
are only `propext`, `Classical.choice`, and `Quot.sound`.

## Consumer boundary and verification

Intended consumer: t93A04. Other proposed consumers: t01A08, t01J04, t92J07,
t96J05. No frozen consumer is changed or closed by this packet. Combine this
rank-zero branch with positive-rank induction where its dimension bound
applies. Larger-source uncovered higher jets and rectangular localization
remain; this is not full rectangular Morse-Sard.

Verify fixture identity, direct compilation, focused build, axiom report,
worklist validity, and frozen-consumer invariance. Stop only if C1 regularity
fails to provide the stated closedness, compact exhaustion fails to transfer
the reviewed compact nullity, or nonstandard axioms are required.
