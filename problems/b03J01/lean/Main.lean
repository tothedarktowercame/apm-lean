import Mathlib

noncomputable section

/-!
# APM b03J01

## Statement repairs

None.

## Encoding notes

Group order and subgroup index are encoded by actual finite cardinality and
`Subgroup.index`; normality and cyclicity use their structural predicates.
-/

def apmB03SmallestPrimeDivisor (p n : ℕ) : Prop :=
  p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q

lemma apm_b03J01_twinPrime_squarefree (p : ℕ) (hp : p.Prime)
    (hp2 : (p + 2).Prime) : Squarefree (p * (p + 2)) := by
  apply (Nat.squarefree_mul ((Nat.coprime_primes hp hp2).2 (by omega))).2
  exact ⟨hp.squarefree, hp2.squarefree⟩

lemma apm_b03J01_isZGroup_of_twinPrime_card
    (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hp2 : (p + 2).Prime) (hcard : Fintype.card G = p * (p + 2)) :
    IsZGroup G := by
  apply IsZGroup.of_squarefree
  rw [Nat.card_eq_fintype_card, hcard]
  exact apm_b03J01_twinPrime_squarefree p hp hp2

lemma apm_b03J01_sylow_normal_of_not_dvd_card
    (G : Type*) [Group G] [Fintype G] (q : ℕ) (hq : q.Prime)
    (hqdvd : ¬q ∣ Fintype.card G) (Q : Sylow q G) :
    (↑Q : Subgroup G).Normal := by
  letI : Fact q.Prime := ⟨hq⟩
  have hcardQ : Nat.card Q = 1 := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd]
    · exact pow_zero q
    · simpa [Nat.card_eq_fintype_card] using hqdvd
  have hbot : (↑Q : Subgroup G) = ⊥ :=
    (Q : Subgroup G).eq_bot_of_card_eq hcardQ
  rw [hbot]
  infer_instance

/-- Why this unblocks `apm_b03j01`: Sylow congruence and divisibility for a
group of order `p * (p + 2)` force every Sylow count to be one.  Packaging
that arithmetic as `Subsingleton (Sylow q G)` is exactly the hypothesis of
`Sylow.normal_of_subsingleton`, after which the standard all-Sylows-normal
criterion gives nilpotence and the existing `IsZGroup` instance gives
cyclicity. -/
theorem apm_b03J01_bridge_sylow_subsingleton_of_twinPrime_card
    (G : Type*) [Group G] [Fintype G]
    (p q : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : q.Prime)
    (hcard : Fintype.card G = p * (p + 2)) :
    Subsingleton (Sylow q G) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  by_cases hqcard : q ∣ Fintype.card G
  · have hsquare : Squarefree (Fintype.card G) := by
      rw [hcard]
      exact apm_b03J01_twinPrime_squarefree p hp hp2
    have hfac : Nat.factorization (Nat.card G) q = 1 := by
      apply Nat.factorization_eq_one_of_squarefree
      · simpa [Nat.card_eq_fintype_card] using hsquare
      · exact hq
      · simpa [Nat.card_eq_fintype_card] using hqcard
    have hcardQ (Q : Sylow q G) : Nat.card Q = q := by
      rw [Q.card_eq_multiplicity, hfac, pow_one]
    have hq_cases : q = p ∨ q = p + 2 := by
      rw [hcard] at hqcard
      rcases hq.dvd_mul.mp hqcard with h | h
      · rcases (Nat.dvd_prime hp).mp h with hq1 | hqp
        · exact False.elim (hq.ne_one hq1)
        · exact Or.inl hqp
      · rcases (Nat.dvd_prime hp2).mp h with hq1 | hqp
        · exact False.elim (hq.ne_one hq1)
        · exact Or.inr hqp
    have hn : Nat.card (Sylow q G) = 1 := by
      let Q : Sylow q G := default
      have hndvd : Nat.card (Sylow q G) ∣ Q.index := Q.card_dvd_index
      have hmod : Nat.card (Sylow q G) ≡ 1 [MOD q] :=
        card_sylow_modEq_one q G
      rcases hq_cases with hqp | hqp
      · subst q
        have hindex : Q.index = p + 2 := by
          have hm := Q.index_mul_card
          rw [hcardQ, Nat.card_eq_fintype_card, hcard] at hm
          apply Nat.eq_of_mul_eq_mul_right hp.pos
          simpa [mul_comm] using hm
        rw [hindex] at hndvd
        rcases (Nat.dvd_prime hp2).mp hndvd with hn1 | hnother
        · exact hn1
        have hpge : 3 ≤ p := by
          have hp2le : 2 ≤ p := hp.two_le
          have hpne2 : p ≠ 2 := by
            intro heq
            subst p
            norm_num at hp2
          omega
        rw [hnother] at hmod
        simp [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 2 < p),
          Nat.mod_eq_of_lt (by omega : 1 < p)] at hmod
      · subst q
        have hindex : Q.index = p := by
          have hm := Q.index_mul_card
          rw [hcardQ, Nat.card_eq_fintype_card, hcard] at hm
          nlinarith [hp.pos]
        rw [hindex] at hndvd
        rcases (Nat.dvd_prime hp).mp hndvd with hn1 | hnother
        · exact hn1
        rw [hnother] at hmod
        simp [Nat.ModEq, Nat.mod_eq_of_lt (by omega : p < p + 2),
          Nat.mod_eq_of_lt (by omega : 1 < p + 2)] at hmod
        exact False.elim (hp.ne_one hmod)
    exact (Nat.card_eq_one_iff_unique.mp hn).1
  · have hQbot (Q : Sylow q G) : (Q : Subgroup G) = ⊥ := by
      have hcardQ : Nat.card Q = 1 := by
        rw [Q.card_eq_multiplicity,
          Nat.factorization_eq_zero_of_not_dvd]
        · exact pow_zero q
        · simpa [Nat.card_eq_fintype_card] using hqcard
      exact (Q : Subgroup G).eq_bot_of_card_eq hcardQ
    exact ⟨fun Q R ↦ Sylow.ext ((hQbot Q).trans (hQbot R).symm)⟩

theorem apm_b03j01
    (G : Type*) [Group G] [Fintype G]
    (p : ℕ) (H : Subgroup G)
    (hp : apmB03SmallestPrimeDivisor p (Fintype.card G))
    (hindex : H.index = p) :
    H.Normal ∧
      ((p + 2).Prime → Fintype.card G = p * (p + 2) → IsCyclic G) := by
  rcases hp with ⟨hpprime, hpdiv, hpmin⟩
  have hcard_ne_one : Fintype.card G ≠ 1 := by
    intro hcard
    rw [hcard] at hpdiv
    exact hpprime.not_dvd_one hpdiv
  have hminfac : (Fintype.card G).minFac = p := by
    apply Nat.le_antisymm
    · exact Nat.minFac_le_of_dvd hpprime.two_le hpdiv
    · apply hpmin (Fintype.card G).minFac
      · exact Nat.minFac_prime hcard_ne_one
      · exact Nat.minFac_dvd (Fintype.card G)
  refine ⟨?_, ?_⟩
  · apply H.normal_of_index_eq_minFac_card
    simpa [Nat.card_eq_fintype_card, hminfac] using hindex
  · intro hp2 hcard
    letI : IsZGroup G :=
      apm_b03J01_isZGroup_of_twinPrime_card G p hpprime hp2 hcard
    letI : Group.IsNilpotent G :=
      ((isNilpotent_of_finite_tfae (G := G)).out 3 0).mp (by
        intro q hq Q
        letI : Subsingleton (Sylow q G) :=
          apm_b03J01_bridge_sylow_subsingleton_of_twinPrime_card
            G p q hpprime hp2 hq.out hcard
        exact Sylow.normal_of_subsingleton Q)
    infer_instance
