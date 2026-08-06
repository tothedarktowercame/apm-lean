import Mathlib

/-! # APM b95J01: powers landing in a finite-index subgroup

## Statement repairs

None.
-/

noncomputable section

/-- The standard non-normal index-three subgroup of `S₃`. -/
def b95j01CounterexampleSubgroup : Subgroup (Equiv.Perm (Fin 3)) :=
  Subgroup.zpowers (Equiv.swap 0 1)

/-- The involution used in the counterexample. -/
def b95j01CounterexampleElement : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 2

/-- Existence and divisibility of the least positive exponent, its stronger
normal-subgroup divisibility property, and the requested explicit counterexample. -/
theorem apm_b95j01
    (G : Type*) [Group G] (H : Subgroup G) [H.FiniteIndex] :
    (∀ g : G, ∃ k : ℕ,
      0 < k ∧ g ^ k ∈ H ∧
      (∀ l : ℕ, 0 < l → g ^ l ∈ H → k ≤ l) ∧
      (∀ m : ℤ, g ^ m ∈ H → (k : ℤ) ∣ m) ∧
      (H.Normal → k ∣ H.index)) ∧
    (¬ b95j01CounterexampleSubgroup.Normal ∧
      b95j01CounterexampleSubgroup.index = 3 ∧
      b95j01CounterexampleElement ∉ b95j01CounterexampleSubgroup ∧
      b95j01CounterexampleElement ^ 2 ∈ b95j01CounterexampleSubgroup ∧
      ¬ 2 ∣ b95j01CounterexampleSubgroup.index) := by
  constructor
  · intro g
    let T : AddSubgroup ℤ :=
      (H.comap ((zpowersHom G) g)).toAddSubgroup'
    have hT (m : ℤ) : m ∈ T ↔ g ^ m ∈ H := by
      rfl
    obtain ⟨n, hnpos, _, hnH⟩ :=
      H.exists_pow_mem_of_index_ne_zero Subgroup.FiniteIndex.index_ne_zero g
    have hnT : (n : ℤ) ∈ T := by
      rw [hT, zpow_natCast]
      exact hnH
    obtain ⟨a, ha⟩ := Int.subgroup_cyclic T
    have ha0 : a ≠ 0 := by
      intro ha0
      subst a
      have hTbot : T = ⊥ := by
        rw [ha]
        ext x
        simp [AddSubgroup.mem_closure_singleton, eq_comm]
      have : (n : ℤ) = 0 := by
        simpa [hTbot] using hnT
      omega
    have hmem (m : ℤ) : g ^ m ∈ H ↔ (a.natAbs : ℤ) ∣ m := by
      rw [← hT, ha, ← AddSubgroup.zmultiples_eq_closure,
        ← Int.zmultiples_natAbs a, Int.mem_zmultiples_iff]
    refine ⟨a.natAbs, Int.natAbs_pos.mpr ha0, ?_, ?_, ?_, ?_⟩
    · rw [← zpow_natCast, hmem]
    · intro l hl hlH
      have hd : a.natAbs ∣ l := by
        exact_mod_cast (hmem (l : ℤ)).mp (by simpa using hlH)
      exact Nat.le_of_dvd hl hd
    · intro m hm
      exact (hmem m).mp hm
    · intro hnormal
      letI : H.Normal := hnormal
      have hd := (hmem (H.index : ℤ)).mp (by
        rw [zpow_natCast]
        exact H.pow_index_mem g)
      exact_mod_cast hd
  · constructor
    · intro hnormal
      have hmem := hnormal.conj_mem
        (Equiv.swap (0 : Fin 3) 1)
        (Subgroup.mem_zpowers (Equiv.swap (0 : Fin 3) 1))
        b95j01CounterexampleElement
      have hnot : b95j01CounterexampleElement * Equiv.swap (0 : Fin 3) 1 *
          b95j01CounterexampleElement⁻¹ ∉ b95j01CounterexampleSubgroup := by
        rw [show b95j01CounterexampleSubgroup =
          Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) from rfl]
        have hord : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 :=
          orderOf_eq_prime (by native_decide) (by native_decide)
        rw [mem_zpowers_iff_mem_range_orderOf, hord]
        native_decide
      exact hnot hmem
    · have hord : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 :=
        orderOf_eq_prime (by native_decide) (by native_decide)
      have hindex : b95j01CounterexampleSubgroup.index = 3 := by
        have hcard := b95j01CounterexampleSubgroup.card_mul_index
        rw [show Nat.card b95j01CounterexampleSubgroup = 2 by
          simpa [b95j01CounterexampleSubgroup] using
            (Nat.card_zpowers (Equiv.swap (0 : Fin 3) 1)).trans hord,
          show Nat.card (Equiv.Perm (Fin 3)) = 6 by
            rw [Nat.card_eq_fintype_card, Fintype.card_perm]
            norm_num] at hcard
        omega
      refine ⟨hindex, ?_, ?_, by omega⟩
      · rw [show b95j01CounterexampleSubgroup =
          Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1) from rfl,
          mem_zpowers_iff_mem_range_orderOf, hord]
        native_decide
      · rw [show b95j01CounterexampleElement ^ 2 = 1 by native_decide]
        exact Subgroup.one_mem _
