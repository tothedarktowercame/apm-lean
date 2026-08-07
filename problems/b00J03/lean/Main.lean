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
  intro p G _ _ hp hcard hnoncomm
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hp0 : 0 < p := hp.pos
  have hGcard : Nat.card G = p ^ 3 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  obtain ⟨k, hkpos, hkcard⟩ :=
    IsPGroup.card_center_eq_prime_pow hGcard (by norm_num)
  have hk_le : k ≤ 3 := by
    apply (Nat.pow_le_pow_iff_right hp1).mp
    rw [← hkcard, ← hGcard]
    exact Nat.le_of_dvd (by rw [hGcard]; positivity)
      (Subgroup.card_subgroup_dvd_card (Subgroup.center G))
  have hk_ne_three : k ≠ 3 := by
    intro hk3
    have hcenter_card : Nat.card (Subgroup.center G) = Nat.card G := by
      rw [hkcard, hk3, hGcard]
    have hcenter_top : Subgroup.center G = ⊤ :=
      (Subgroup.card_eq_iff_eq_top (Subgroup.center G)).mp hcenter_card
    have hcomm_bot : commutator G = ⊥ :=
      (commutator_eq_bot_iff_center_eq_top G).2 hcenter_top
    exact (apm_b00j03_commutator_ne_bot hnoncomm) hcomm_bot
  have hk_ne_two : k ≠ 2 := by
    intro hk2
    have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center G)
    have hqcard : Nat.card (G ⧸ Subgroup.center G) = p := by
      apply Nat.eq_of_mul_eq_mul_right (by positivity : 0 < p ^ 2)
      calc
        Nat.card (G ⧸ Subgroup.center G) * p ^ 2
            = Nat.card (G ⧸ Subgroup.center G) *
                Nat.card (Subgroup.center G) := by rw [hkcard, hk2]
        _ = Nat.card G := hprod.symm
        _ = p * p ^ 2 := by rw [hGcard]; ring
    letI : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hqcard
    letI : CommGroup G := commGroupOfCyclicCenterQuotient
      (QuotientGroup.mk' (Subgroup.center G)) (by
        rw [QuotientGroup.ker_mk'])
    obtain ⟨x, y, hxy⟩ := hnoncomm
    exact hxy (mul_comm x y)
  have hk : k = 1 := by omega
  have hcenter_card : Nat.card (Subgroup.center G) = p := by
    simpa [hk] using hkcard
  have hprod := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center G)
  have hqcard : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_right hp0
    calc
      Nat.card (G ⧸ Subgroup.center G) * p
          = Nat.card (G ⧸ Subgroup.center G) *
              Nat.card (Subgroup.center G) := by rw [hcenter_card]
      _ = Nat.card G := hprod.symm
      _ = p ^ 2 * p := by rw [hGcard]; ring
  have hquot_comm : Std.Commutative
      (fun x y : G ⧸ Subgroup.center G => x * y) :=
    ⟨IsPGroup.commutative_of_card_eq_prime_sq hqcard⟩
  have hle : commutator G ≤ Subgroup.center G :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hquot_comm
  exact ⟨hcenter_card,
    apm_b00j03_eq_of_le_center_of_prime_card hp hcenter_card hle
      (apm_b00j03_commutator_ne_bot hnoncomm)⟩
