# Proof Outline: b99A02

The canonical Lean attempt proves that the specified Sylow 5-subgroup is
normal by a complete Sylow count. One sorry remains for the quotient cascade,
normality of the Sylow 29-subgroup, and the final order-175 subgroup.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b99A02.md`

## Formal progress

- `Sylow.card_eq_multiplicity`, `Sylow.card_dvd_index`, and
  `card_sylow_modEq_one` show there is exactly one Sylow 5-subgroup.
- `apm_b99A02_normal_comap_mk_and_le` proves that a normal subgroup of
  `G ⧸ P` pulls back to a normal subgroup of `G` containing `P`.
- `apm_b99A02_card_comap_mk`, using
  `QuotientGroup.card_preimage_mk`, proves the exact pullback formula
  `Nat.card (S.comap mk') = Nat.card N * Nat.card S`.

## Remaining bridge

Count the Sylow 29-subgroups of `G ⧸ P` and prove the quotient Sylow has
cardinality 29 (the pullback then has cardinality `25 * 29` by the helper),
and transport uniqueness back to the specified `Q`. Construct
`K = P R`, perform its product-cardinality calculation, and prove its
normality is equivalent to commutativity of `G`.
