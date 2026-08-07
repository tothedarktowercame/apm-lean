# Proof Outline: b99A02

The canonical Lean attempt proves that the specified Sylow 5-subgroup is
normal and constructs the required normal subgroup of order `25 * 29`. One
sorry remains for normality of the specified Sylow 29-subgroup and the final
order-175 subgroup.

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
- `apm_b99A02_sylow29_unique_of_card_203` and
  `apm_b99A02_sylow29_normal_of_card_203` close the quotient Sylow count.
  The main proof computes `|G ⩸ P| = 203`, pulls this subgroup back, and proves
  the pullback is normal with cardinality `5^2 * 29`.

## Remaining bridge

Transport the pullback's Sylow uniqueness to the specified `Q`. Construct
`K = P R`, perform its product-cardinality calculation, and prove its
normality is equivalent to commutativity of `G`.
