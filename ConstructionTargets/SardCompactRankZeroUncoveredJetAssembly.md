# Compact rank-zero uncovered-jet assembly

Provides `compact_rankZero_image_zero_of_uncovered_higherJets`.
The module is byte-identical to the accepted fixture, SHA-256
`1d98a23b2a3b47f93f7b785b41f45474e7d4fbbf86aa18f9a2fab16d80d47885`.

## Statement and proof

For a compact rank-zero source set K and a globally C^(k+1) map, assume
classical Sard order admissibility. Source and target are nontrivial
finite-dimensional real inner-product Borel spaces, with a proper source
and the specified target add-Haar measure. Nullity of f(K) follows provided
the images of first-nonzero-j-jet loci are null for every 2 <= j <= k+1
satisfying j*targetDim <= sourceDim-1. These remaining nullity hypotheses
are explicit; they are not consequences established by this theorem.

The proof invokes the reviewed admissible compact rank-zero assembly and
splits each higher-jet obligation at the strict Taylor dimension bound.
For a covered order, global regularity is restricted to order j, with the
natural predecessor identity (j-1)+1=j justified by j>=2. The reviewed
all-source Taylor nullity theorem discharges this obligation. Complementary
orders use exactly the supplied uncovered-jet hypothesis. The target measure,
source set, rank-zero condition, admissibility, and finite jet range are
preserved throughout.

Observed dependencies are `SardCompactRankZeroAdmissibleJetAssembly` and
`SardFirstNonzeroJetAllSourceTaylorNullity`. Expected axioms are only
`propext`, `Classical.choice`, and `Quot.sound`.

## Consumer boundary and verification

Intended consumer: t93A04. Other proposed consumers: t01A08, t01J04, t92J07,
t96J05. No frozen consumer is changed or closed by this infrastructure packet.
Prove nullity for the remaining orders j with j*targetDim <= sourceDim-1,
then complete rank-zero localization, rectangular induction, and exhaustion.
This conditional assembly is not a proof of full rectangular Morse-Sard.

Verify fixture identity, direct compilation, focused build, axiom report,
worklist validity, and frozen-consumer invariance. Stop only if regularity
restriction and strict-surplus nullity fail on the complementary range,
compact assembly fails under the stated hypotheses, or nonstandard axioms
are required.
