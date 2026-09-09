# Remaining-order admissibility boundary

This module classifies when classical Sard admissibility survives loss of
derivatives. For natural dimensions m, t, order r, and loss l with l <= r,
`remainingOrder_admissible_iff` identifies admissibility at order r-l with
`m + l < t + r`. For m > 0, `codimensionOne_remainingOrder_admissible_iff`
identifies admissibility after also reducing the source dimension by one
with `m + l ≤ t + r`. The hypotheses control truncated natural subtraction.

`classical_admissibility_does_not_cover_all_jet_losses` verifies m=3, t=1,
r=3, l=2: the original dimensions and order are admissible, but source
dimension 2 and remaining order 1 are not. This refutes only automatic
inheritance of admissibility for all jet losses. It neither exhibits a map
violating Morse-Sard nor refutes the conditional variable-order theorem.

The observed import is `SardClassicalRegularityAdmissibility`. The reviewed
`SardFiniteOrderHigherJetVariableInduction` motivates this boundary: its
remaining-order lower-dimensional nullity hypotheses cannot simply be
inferred from classical admissibility. Higher jets outside the admissible
range need a different analytic argument. That repair and subsequent
compact rank-zero assembly and localization remain unresolved.

The source is byte-identical to the accepted fixture
`/tmp/SardRemainingOrderAdmissibilityBoundaryProbe.lean`, SHA-256
`f07f1562bd70e452475f1986ccc0514d491dcb14d7a5a6e8efdfc4d903572ace`.
All three declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
The intended consumer is t93A04; additional proposed consumers are t01A08,
t01J04, t92J07, and t96J05. No frozen consumer is changed or closed here.

The stop boundary for this packet is falsity of its arithmetic equivalences
or witness, or a need for nonstandard axioms. The witness is not grounds
for stopping rectangular Morse-Sard as mathematically refuted.
