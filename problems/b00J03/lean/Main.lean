import Mathlib

/-!
# APM b00J03

## Statement repairs

None.

## Encoding questions

None. Nonabelianness is stated by an explicit pair of noncommuting elements,
and `commutator G` is Mathlib's commutator subgroup `[G,G]`.
-/

/-- Noncommutativity forces the derived subgroup to be nontrivial. -/
lemma apm_b00j03_commutator_ne_bot
    {G : Type*} [Group G] (hG : ∃ x y : G, x * y ≠ y * x) :
    commutator G ≠ ⊥ := by
  rw [ne_eq, commutator_eq_bot_iff_center_eq_top]
  intro hcenter
  obtain ⟨x, y, hxy⟩ := hG
  have hx : x ∈ Subgroup.center G := hcenter.symm ▸ (by simp)
  exact hxy ((Subgroup.mem_center_iff.mp hx) y).symm

/-- A nontrivial subgroup contained in a prime-cardinality subgroup is the
whole subgroup. This is the final cardinality squeeze in the paper proof. -/
lemma apm_b00j03_eq_of_le_center_of_prime_card
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : Nat.Prime p) (hcard : Nat.card (Subgroup.center G) = p)
    (hle : commutator G ≤ Subgroup.center G) (hne : commutator G ≠ ⊥) :
    Subgroup.center G = commutator G := by
  let D : Subgroup (Subgroup.center G) := (commutator G).subgroupOf (Subgroup.center G)
  have hprime : Nat.Prime (Nat.card (Subgroup.center G)) := hcard.symm ▸ hp
  letI : Fact (Nat.Prime (Nat.card (Subgroup.center G))) := ⟨hprime⟩
  have hD : D = ⊤ := by
    rcases D.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exfalso
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have hxD : ⟨x, hle hx⟩ ∈ D := hx
      rw [hbot] at hxD
      simpa using hxD
    · exact htop
  apply le_antisymm
  · intro z hz
    have : ⟨z, hz⟩ ∈ D := hD.symm ▸ (by simp)
    exact this
  · exact hle

theorem apm_b00j03 :
    ∀ (p : ℕ) (G : Type*) [Group G] [Fintype G],
      Nat.Prime p →
      Fintype.card G = p ^ 3 →
      (∃ x y : G, x * y ≠ y * x) →
      Nat.card (Subgroup.center G) = p ∧
        Subgroup.center G = commutator G := by
  /-
  Boundary (closer hop 1): Mathlib's `IsPGroup.card_center_eq_prime_pow`
  packages the class-equation step: the center has cardinality `p^k` for
  some positive `k`.  Lagrange then gives `k ≤ 3`.  The cases `k = 3`
  and `k = 2` must be excluded: the former makes the center all of `G`;
  the latter makes `G/Z(G)` prime-order and hence cyclic, so
  `commGroupOfCyclicCenterQuotient` makes `G` abelian.

  This hop formally closes the two steps after that arithmetic exclusion.
  `apm_b00j03_commutator_ne_bot` converts the supplied noncommuting pair
  into `[G,G] ≠ ⊥`.  Once the quotient `G/Z(G)` is shown commutative,
  `Subgroup.Normal.quotient_commutative_iff_commutator_le` gives
  `[G,G] ≤ Z(G)`; `apm_b00j03_eq_of_le_center_of_prime_card` then proves
  equality from `|Z(G)| = p`.  Searches of `LEMMA-INDEX.md`, all problem
  artifacts, `ConstructionTargets/`, and Mathlib found no theorem
  specializing the remaining prime-power cardinality exclusion to order
  `p^3`; it remains the sole open bridge.
  -/
  sorry
