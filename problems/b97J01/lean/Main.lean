import Mathlib

open scoped commutatorElement

/-!
# APM b97J01 — solvable and nilpotent groups; finite p-groups

Solvability and nilpotence use Mathlib's standard derived series and lower
central series.  The examples are the concrete permutation groups `S₅` and
`S₃`, and the final clauses are the usual center and nilpotence theorems for
finite groups of prime-power order.

## Statement repairs

None.

## Encoding questions

None.
-/

def apm_b97j01_solvable (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, derivedSeries G n = ⊥

def apm_b97j01_nilpotent (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, lowerCentralSeries G n = ⊥

theorem apm_b97j01 :
    ¬apm_b97j01_solvable (Equiv.Perm (Fin 5)) ∧
    apm_b97j01_solvable (Equiv.Perm (Fin 3)) ∧
    ¬apm_b97j01_nilpotent (Equiv.Perm (Fin 3)) ∧
    (∀ (G : Type) [Group G] [Fintype G] (p n : ℕ),
      p.Prime → Fintype.card G = p ^ n → 1 < p ^ n →
        Subgroup.center G ≠ ⊥) ∧
    (∀ (G : Type) [Group G] [Fintype G] (p n : ℕ),
      p.Prime → Fintype.card G = p ^ n →
        apm_b97j01_nilpotent G) := by
  have hs3 : apm_b97j01_solvable (Equiv.Perm (Fin 3)) := by
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.card_fin]
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    letI : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
    letI : CommGroup (alternatingGroup (Fin 3)) := IsCyclic.commGroup
    have hs : IsSolvable (Equiv.Perm (Fin 3)) :=
      solvable_of_ker_le_range (G := Equiv.Perm (Fin 3))
        (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign (by
        rw [← alternatingGroup_eq_sign_ker]
        rw [Subgroup.range_subtype])
    exact hs.solvable
  have hn3 : ¬apm_b97j01_nilpotent (Equiv.Perm (Fin 3)) := by
    intro h
    rcases h with ⟨n, hn⟩
    have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.card_fin]
    letI : Fact (Nat.card (alternatingGroup (Fin 3))).Prime :=
      ⟨hcard.symm ▸ by decide⟩
    have prime_sandwich (H : Subgroup (Equiv.Perm (Fin 3)))
        (hH : H ≤ alternatingGroup (Fin 3)) (hH0 : H ≠ ⊥) :
        H = alternatingGroup (Fin 3) := by
      let K := H.comap (alternatingGroup (Fin 3)).subtype
      have hK0 : K ≠ ⊥ := by
        intro hK
        apply hH0
        have hHr : H ≤ (alternatingGroup (Fin 3)).subtype.range := by
          rwa [Subgroup.range_subtype]
        rw [← Subgroup.map_comap_eq_self hHr]
        change Subgroup.map (alternatingGroup (Fin 3)).subtype K = ⊥
        rw [hK, Subgroup.map_bot]
      have hKtop : K = ⊤ := K.eq_bot_or_eq_top_of_prime_card.resolve_left hK0
      apply le_antisymm hH
      intro x hx
      have hxK : (⟨x, hx⟩ : alternatingGroup (Fin 3)) ∈ K := by
        rw [hKtop]; exact Subgroup.mem_top _
      exact hxK
    have hcomm_ne : commutator (Equiv.Perm (Fin 3)) ≠ ⊥ := by
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      refine ⟨⟨⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩, ?_⟩
      decide
    have hcomm : commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) :=
      prime_sandwich _ alternatingGroup.commutator_perm_le hcomm_ne
    have halt_ne : ⁅alternatingGroup (Fin 3),
        (⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆ ≠ ⊥ := by
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      let a : Equiv.Perm (Fin 3) :=
        { toFun := ![1, 2, 0], invFun := ![2, 0, 1],
          left_inv := by decide, right_inv := by decide }
      have ha : a ∈ alternatingGroup (Fin 3) := by
        change Equiv.Perm.sign a = 1
        decide
      refine ⟨⟨⁅a, Equiv.swap (0 : Fin 3) 1⁆,
        Subgroup.commutator_mem_commutator ha (Subgroup.mem_top _)⟩, ?_⟩
      have hval : ⁅a, Equiv.swap (0 : Fin 3) 1⁆ ≠ 1 := by
        dsimp [a]
        decide
      intro heq
      exact hval (congrArg Subtype.val heq)
    have halt : ⁅alternatingGroup (Fin 3),
        (⊤ : Subgroup (Equiv.Perm (Fin 3)))⁆ = alternatingGroup (Fin 3) :=
      prime_sandwich _ (Subgroup.commutator_le_left _ _) halt_ne
    have hstable : ∀ m : ℕ, lowerCentralSeries (Equiv.Perm (Fin 3)) (m + 1) =
        commutator (Equiv.Perm (Fin 3)) := by
      intro m
      induction m with
      | zero => exact lowerCentralSeries_one
      | succ m ih =>
          rw [show m.succ + 1 = (m + 1) + 1 by omega]
          change ⁅lowerCentralSeries (Equiv.Perm (Fin 3)) (m + 1), ⊤⁆ = _
          rw [ih]
          rw [hcomm, halt]
    cases n with
    | zero =>
        rw [lowerCentralSeries_zero] at hn
        exact top_ne_bot hn
    | succ n => exact hcomm_ne ((hstable n).symm.trans hn)
  refine ⟨?_, hs3, hn3, ?_, ?_⟩
  · exact fun h => Equiv.Perm.fin_5_not_solvable ⟨h⟩
  · intro G _ _ p n hp hcard hnontrivial
    letI : Fact p.Prime := ⟨hp⟩
    have hG : IsPGroup p G := IsPGroup.of_card (by simpa [Nat.card_eq_fintype_card] using hcard)
    haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by simpa [hcard] using hnontrivial)
    exact ne_of_gt hG.bot_lt_center
  · intro G _ _ p n hp hcard
    letI : Fact p.Prime := ⟨hp⟩
    have hG : IsPGroup p G := IsPGroup.of_card (by simpa [Nat.card_eq_fintype_card] using hcard)
    exact nilpotent_iff_lowerCentralSeries.mp hG.isNilpotent

#print axioms apm_b97j01
