# Proof Outline: b03J01

The Lean proof closes the normality conclusion: the least-prime-divisor
hypothesis identifies `p` with `minFac |G|`, and Mathlib's
`Subgroup.normal_of_index_eq_minFac_card` applies to the index hypothesis.

For the conditional cyclicity conclusion, the proof now also establishes
that `p * (p + 2)` is squarefree and installs `IsZGroup G` using
`IsZGroup.of_squarefree`.

## Remaining boundary

One sorry remains. It is the Sylow-counting bridge needed to show every
Sylow subgroup is normal. The intended completion uses
`Sylow.card_sylow_modEq_one` and the relevant divisibility bound to prove
uniqueness for the `p`- and `(p+2)`-Sylows, then
`isNilpotent_of_finite_tfae`. The existing `IsZGroup` and resulting
nilpotence give `IsCyclic G` through Mathlib's instance.

Closer hop 3 proves the absent-prime branch as
`apm_b03J01_sylow_normal_of_not_dvd_card`: if `q ∤ |G|`, then
`Sylow.card_eq_multiplicity` makes every Sylow `q`-subgroup have cardinality
one, hence it is bottom and normal. The remaining work is now confined to
`q = p` and `q = p + 2`, where the congruence/divisibility arithmetic must
produce `Subsingleton (Sylow q G)`.
