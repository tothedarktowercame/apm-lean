# Proof Outline: b00J03

The frozen theorem is fully proved in `lean/Main.lean`.

1. `apm_b00j03_commutator_ne_bot` proves that an explicit noncommuting pair
   forces `commutator G ≠ ⊥`, using
   `commutator_eq_bot_iff_center_eq_top`.
2. `apm_b00j03_eq_of_le_center_of_prime_card` proves that a nontrivial
   commutator subgroup contained in a center of prime cardinality equals the
   center, using `Subgroup.eq_bot_or_eq_top_of_prime_card`.

The order-`p^3` cardinality argument uses Mathlib's
`IsPGroup.card_center_eq_prime_pow`, which gives `|Z(G)| = p^k` with `0 < k`.
Lagrange bounds `k ≤ 3`; the proof excludes `k = 3` (the group is
abelian) and `k = 2` (the center quotient has prime cardinality, hence is
cyclic, again making the group abelian). Once `k = 1`, quotient cardinality
is `p^2`, `IsPGroup.commutative_of_card_eq_prime_sq` makes the quotient
commutative, and
`Subgroup.Normal.quotient_commutative_iff_commutator_le` supplies the
containment needed by helper 2.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b00J03.md`

The explicit noncommuting pair rules out both abelian cases and also proves
the commutator subgroup is nontrivial. Prime cardinality of the center then
forces the commutator subgroup to equal it.
