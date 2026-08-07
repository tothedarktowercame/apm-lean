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

## Remaining bridge

Count the Sylow 29-subgroups of `G ⧸ P`, prove the pullback has cardinality
`25 * 29`, and transport uniqueness back to the specified `Q`. Construct
`K = P R`, perform its product-cardinality calculation, and prove its
normality is equivalent to commutativity of `G`.
