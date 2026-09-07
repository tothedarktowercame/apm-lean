import Mathlib

/-!
# APM b97A01: `S₄` and groups of order 24

## Statement repairs

None.

## Encoding questions

None. The conjugacy classes are represented by explicit permutations of each
cycle type. The requested example is the literal matrix group `SL₂(ZMod 3)`.
-/

open Equiv Equiv.Perm Subgroup

noncomputable section

abbrev apm_b97A01_S4 := Equiv.Perm (Fin 4)

def apm_b97A01_transposition : apm_b97A01_S4 := swap 0 1

def apm_b97A01_doubleTransposition : apm_b97A01_S4 :=
  swap 0 1 * swap 2 3

def apm_b97A01_threeCycle : apm_b97A01_S4 :=
  swap 0 1 * swap 1 2

def apm_b97A01_fourCycle : apm_b97A01_S4 :=
  swap 0 1 * swap 1 2 * swap 2 3

/-- The Klein four subgroup, included into `S₄` from `A₄`. -/
def apm_b97A01_V4 : Subgroup apm_b97A01_S4 :=
  (alternatingGroup.kleinFour (Fin 4)).map (alternatingGroup (Fin 4)).subtype

abbrev apm_b97A01_SL23 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

/-- The concrete special linear group in the example has order `24`. -/
lemma apm_b97A01_SL23_card : Nat.card apm_b97A01_SL23 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- Cycle types of the four nonidentity class representatives. -/
lemma apm_b97A01_representative_cycleTypes :
    apm_b97A01_transposition.cycleType = {2} ∧
    apm_b97A01_doubleTransposition.cycleType = {2, 2} ∧
    apm_b97A01_threeCycle.cycleType = {3} ∧
    apm_b97A01_fourCycle.cycleType = {4} := by
  decide

/-- Each displayed representative characterizes its conjugacy class by its
cycle type. -/
lemma apm_b97A01_conjugacy_classification :
    ∀ σ : apm_b97A01_S4,
      (IsConj 1 σ ↔ σ.cycleType = {}) ∧
      (IsConj apm_b97A01_transposition σ ↔ σ.cycleType = {2}) ∧
      (IsConj apm_b97A01_doubleTransposition σ ↔
        σ.cycleType = {2, 2}) ∧
      (IsConj apm_b97A01_threeCycle σ ↔ σ.cycleType = {3}) ∧
      (IsConj apm_b97A01_fourCycle σ ↔ σ.cycleType = {4}) := by
  intro σ
  rw [Equiv.Perm.isConj_iff_cycleType_eq,
    Equiv.Perm.isConj_iff_cycleType_eq,
    Equiv.Perm.isConj_iff_cycleType_eq,
    Equiv.Perm.isConj_iff_cycleType_eq,
    Equiv.Perm.isConj_iff_cycleType_eq]
  rcases apm_b97A01_representative_cycleTypes with ⟨htrans, hdouble, hthree, hfour⟩
  simp [htrans, hdouble, hthree, hfour, eq_comm]

/-- The five conjugacy classes have the advertised cardinalities.  This uses
Mathlib's centralizer formula `Equiv.Perm.card_isConj_eq`. -/
lemma apm_b97A01_conjugacy_class_cards :
    Nat.card {σ : apm_b97A01_S4 // IsConj 1 σ} = 1 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_transposition σ} = 6 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_doubleTransposition σ} = 3 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_threeCycle σ} = 8 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_fourCycle σ} = 6 := by
  rcases apm_b97A01_representative_cycleTypes with ⟨htrans, hdouble, hthree, hfour⟩
  constructor
  · simpa using (Equiv.Perm.card_isConj_eq (g := (1 : apm_b97A01_S4)))
  constructor
  · simpa [htrans] using
      (Equiv.Perm.card_isConj_eq (g := apm_b97A01_transposition))
  constructor
  · simpa [hdouble] using
      (Equiv.Perm.card_isConj_eq (g := apm_b97A01_doubleTransposition))
  constructor
  · simpa [hthree] using
      (Equiv.Perm.card_isConj_eq (g := apm_b97A01_threeCycle))
  · simpa [hfour] using
      (Equiv.Perm.card_isConj_eq (g := apm_b97A01_fourCycle))

/-- Every permutation of four letters lies in one of the five displayed
conjugacy classes. -/
lemma apm_b97A01_conjugacy_exhaustive :
    ∀ σ : apm_b97A01_S4,
      IsConj 1 σ ∨ IsConj apm_b97A01_transposition σ ∨
        IsConj apm_b97A01_doubleTransposition σ ∨
        IsConj apm_b97A01_threeCycle σ ∨
        IsConj apm_b97A01_fourCycle σ := by
  decide

/-- The characterization and exhaustiveness portions of the frozen first
conjunct, assembled from the structural cycle-type theorem and the finite
four-letter exhaustion. -/
lemma apm_b97A01_complete_conjugacy_classification :
    ∀ σ : apm_b97A01_S4,
      (IsConj 1 σ ↔ σ.cycleType = {}) ∧
      (IsConj apm_b97A01_transposition σ ↔ σ.cycleType = {2}) ∧
      (IsConj apm_b97A01_doubleTransposition σ ↔ σ.cycleType = {2, 2}) ∧
      (IsConj apm_b97A01_threeCycle σ ↔ σ.cycleType = {3}) ∧
      (IsConj apm_b97A01_fourCycle σ ↔ σ.cycleType = {4}) ∧
      (IsConj 1 σ ∨ IsConj apm_b97A01_transposition σ ∨
        IsConj apm_b97A01_doubleTransposition σ ∨
        IsConj apm_b97A01_threeCycle σ ∨
        IsConj apm_b97A01_fourCycle σ) := by
  intro σ
  rcases apm_b97A01_conjugacy_classification σ with
    ⟨hone, htrans, hdouble, hthree, hfour⟩
  exact ⟨hone, htrans, hdouble, hthree, hfour,
    apm_b97A01_conjugacy_exhaustive σ⟩

/-- Why this unblocks `apm_b97a01`: this is the complete normal-subgroup
lattice of `S₄`. It is a structural consequence of conjugacy-class closure
and the already compiled five-class classification. -/
lemma apm_b97A01_V4_normal : apm_b97A01_V4.Normal := by
  unfold apm_b97A01_V4
  letI : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (by simp)
  infer_instance

lemma apm_b97A01_V4_card : Nat.card apm_b97A01_V4 = 4 := by
  unfold apm_b97A01_V4
  rw [Subgroup.card_map_of_injective]
  · exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  · exact (alternatingGroup (Fin 4)).subtype_injective

lemma apm_b97A01_A4_card : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [nat_card_alternatingGroup]
  norm_num

lemma apm_b97A01_named_subgroups_normal
    (N : Subgroup apm_b97A01_S4)
    (hN : N = ⊥ ∨ N = apm_b97A01_V4 ∨
      N = alternatingGroup (Fin 4) ∨ N = ⊤) : N.Normal := by
  rcases hN with rfl | rfl | rfl | rfl
  · infer_instance
  · exact apm_b97A01_V4_normal
  · infer_instance
  · infer_instance

lemma apm_b97A01_normal_mem_iff_of_isConj
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    {a b : apm_b97A01_S4} (hab : IsConj a b) :
    a ∈ N ↔ b ∈ N := by
  have forward : ∀ {x y : apm_b97A01_S4}, IsConj x y → x ∈ N → y ∈ N := by
    intro x y hxy hx
    rcases hxy with ⟨c, hc⟩
    have hm := hN.conj_mem x hx (c : apm_b97A01_S4)
    rw [SemiconjBy] at hc
    convert hm using 1
    rw [hc]
    simp
  exact ⟨forward hab, forward hab.symm⟩

lemma apm_b97A01_normal_eq_top_of_transposition_mem
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    (htrans : apm_b97A01_transposition ∈ N) : N = ⊤ := by
  rw [eq_top_iff, ← Equiv.Perm.closure_isSwap, Subgroup.closure_le]
  intro σ hσ
  have hcycle : σ.cycleType = {2} := Equiv.Perm.isSwap_iff_cycleType.mp hσ
  have hconj : IsConj apm_b97A01_transposition σ :=
    (apm_b97A01_conjugacy_classification σ).2.1.mpr hcycle
  exact (apm_b97A01_normal_mem_iff_of_isConj N hN hconj).mp htrans

lemma apm_b97A01_alternating_le_of_threeCycle_mem
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    (hthree : apm_b97A01_threeCycle ∈ N) :
    alternatingGroup (Fin 4) ≤ N := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hcycle : σ.cycleType = {3} := hσ.cycleType
  have hconj : IsConj apm_b97A01_threeCycle σ :=
    (apm_b97A01_conjugacy_classification σ).2.2.2.1.mpr hcycle
  exact (apm_b97A01_normal_mem_iff_of_isConj N hN hconj).mp hthree

lemma apm_b97A01_V4_le_of_doubleTransposition_mem
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    (hdouble : apm_b97A01_doubleTransposition ∈ N) :
    apm_b97A01_V4 ≤ N := by
  intro σ hσ
  rw [apm_b97A01_V4, Subgroup.mem_map] at hσ
  rcases hσ with ⟨τ, hτ, rfl⟩
  rw [← SetLike.mem_coe,
    alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)] at hτ
  rcases hτ with hτ | hτ
  · rw [Set.mem_singleton_iff] at hτ
    subst τ
    exact N.one_mem
  · have hcycle : (τ : apm_b97A01_S4).cycleType = {2, 2} := hτ
    have hconj : IsConj apm_b97A01_doubleTransposition
        (τ : apm_b97A01_S4) :=
      (apm_b97A01_conjugacy_classification τ).2.2.1.mpr hcycle
    exact (apm_b97A01_normal_mem_iff_of_isConj N hN hconj).mp hdouble

lemma apm_b97A01_doubleTransposition_mem_V4 :
    apm_b97A01_doubleTransposition ∈ apm_b97A01_V4 := by
  rw [apm_b97A01_V4, Subgroup.mem_map]
  let d : alternatingGroup (Fin 4) :=
    ⟨apm_b97A01_doubleTransposition, by
      change Equiv.Perm.sign apm_b97A01_doubleTransposition = 1
      decide⟩
  refine ⟨d, ?_, rfl⟩
  rw [← SetLike.mem_coe,
    alternatingGroup.coe_kleinFour_of_card_eq_four (by simp)]
  exact Or.inr apm_b97A01_representative_cycleTypes.2.1

lemma apm_b97A01_normal_eq_top_of_fourCycle_mem
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    (hfour : apm_b97A01_fourCycle ∈ N) : N = ⊤ := by
  have hsqconj : IsConj apm_b97A01_doubleTransposition
      (apm_b97A01_fourCycle ^ 2) := by decide
  have hsquare : apm_b97A01_fourCycle ^ 2 ∈ N := N.pow_mem hfour 2
  have hdouble : apm_b97A01_doubleTransposition ∈ N :=
    (apm_b97A01_normal_mem_iff_of_isConj N hN hsqconj).mpr hsquare
  have hprod : apm_b97A01_fourCycle * apm_b97A01_doubleTransposition ∈ N :=
    N.mul_mem hfour hdouble
  have hswap : (apm_b97A01_fourCycle *
      apm_b97A01_doubleTransposition).IsSwap := by
    rw [Equiv.Perm.isSwap_iff_cycleType]
    decide
  have hconj : IsConj apm_b97A01_transposition
      (apm_b97A01_fourCycle * apm_b97A01_doubleTransposition) :=
    (apm_b97A01_conjugacy_classification _).2.1.mpr
      (Equiv.Perm.isSwap_iff_cycleType.mp hswap)
  apply apm_b97A01_normal_eq_top_of_transposition_mem N hN
  exact (apm_b97A01_normal_mem_iff_of_isConj N hN hconj).mpr hprod

lemma apm_b97A01_normal_eq_bot_of_representatives_not_mem
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    (ht : apm_b97A01_transposition ∉ N)
    (hd : apm_b97A01_doubleTransposition ∉ N)
    (h3 : apm_b97A01_threeCycle ∉ N)
    (h4 : apm_b97A01_fourCycle ∉ N) : N = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rcases apm_b97A01_conjugacy_exhaustive σ with h | h | h | h | h
  · rw [Subgroup.mem_bot, ← isConj_one_right]
    exact h
  · exact False.elim (ht ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))
  · exact False.elim (hd ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))
  · exact False.elim (h3 ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))
  · exact False.elim (h4 ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))

lemma apm_b97A01_normal_le_V4_of_odd_and_three_not_mem
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    (ht : apm_b97A01_transposition ∉ N)
    (h3 : apm_b97A01_threeCycle ∉ N)
    (h4 : apm_b97A01_fourCycle ∉ N) : N ≤ apm_b97A01_V4 := by
  intro σ hσ
  rcases apm_b97A01_conjugacy_exhaustive σ with h | h | h | h | h
  · rw [isConj_one_right] at h
    simpa [h]
  · exact False.elim (ht ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))
  · exact (apm_b97A01_normal_mem_iff_of_isConj apm_b97A01_V4
      apm_b97A01_V4_normal h).mp apm_b97A01_doubleTransposition_mem_V4
  · exact False.elim (h3 ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))
  · exact False.elim (h4 ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))

lemma apm_b97A01_normal_le_A4_of_odd_not_mem
    (N : Subgroup apm_b97A01_S4) (hN : N.Normal)
    (ht : apm_b97A01_transposition ∉ N)
    (h4 : apm_b97A01_fourCycle ∉ N) :
    N ≤ alternatingGroup (Fin 4) := by
  have hd : apm_b97A01_doubleTransposition ∈ alternatingGroup (Fin 4) := by
    change Equiv.Perm.sign apm_b97A01_doubleTransposition = 1
    decide
  have hthree : apm_b97A01_threeCycle ∈ alternatingGroup (Fin 4) := by
    change Equiv.Perm.sign apm_b97A01_threeCycle = 1
    decide
  intro σ hσ
  rcases apm_b97A01_conjugacy_exhaustive σ with h | h | h | h | h
  · rw [isConj_one_right] at h
    simpa [h]
  · exact False.elim (ht ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))
  · exact (apm_b97A01_normal_mem_iff_of_isConj (alternatingGroup (Fin 4))
      inferInstance h).mp hd
  · exact (apm_b97A01_normal_mem_iff_of_isConj (alternatingGroup (Fin 4))
      inferInstance h).mp hthree
  · exact False.elim (h4 ((apm_b97A01_normal_mem_iff_of_isConj N hN h).mpr hσ))

theorem apm_b97A01_bridge_normal_subgroups :
    ∀ N : Subgroup apm_b97A01_S4,
      N.Normal ↔
        N = ⊥ ∨ N = apm_b97A01_V4 ∨
        N = alternatingGroup (Fin 4) ∨ N = ⊤ := by
  intro N
  constructor
  · intro hN
    by_cases ht : apm_b97A01_transposition ∈ N
    · exact Or.inr (Or.inr (Or.inr
        (apm_b97A01_normal_eq_top_of_transposition_mem N hN ht)))
    by_cases h4 : apm_b97A01_fourCycle ∈ N
    · exact Or.inr (Or.inr (Or.inr
        (apm_b97A01_normal_eq_top_of_fourCycle_mem N hN h4)))
    by_cases h3 : apm_b97A01_threeCycle ∈ N
    · exact Or.inr (Or.inr (Or.inl (le_antisymm
        (apm_b97A01_normal_le_A4_of_odd_not_mem N hN ht h4)
        (apm_b97A01_alternating_le_of_threeCycle_mem N hN h3))))
    by_cases hd : apm_b97A01_doubleTransposition ∈ N
    · exact Or.inr (Or.inl (le_antisymm
        (apm_b97A01_normal_le_V4_of_odd_and_three_not_mem N hN ht h3 h4)
        (apm_b97A01_V4_le_of_doubleTransposition_mem N hN hd)))
    · exact Or.inl (apm_b97A01_normal_eq_bot_of_representatives_not_mem
        N hN ht hd h3 h4)
  · exact apm_b97A01_named_subgroups_normal N

/-- Why this unblocks `apm_b97a01`: this supplies the requested derived-series
property of `S₄`, for example via the normal series
`1 ◁ V₄ ◁ A₄ ◁ S₄` with abelian factors. -/
theorem apm_b97A01_bridge_S4_solvable :
    IsSolvable apm_b97A01_S4 := by
  have h1 : derivedSeries apm_b97A01_S4 1 ≤
      alternatingGroup (Fin 4) := by
    exact alternatingGroup.commutator_perm_le
  have h2 : derivedSeries apm_b97A01_S4 2 ≤ apm_b97A01_V4 := by
    rw [derivedSeries_succ]
    refine (Subgroup.commutator_mono h1 h1).trans_eq ?_
    rw [← Subgroup.map_subtype_commutator,
      ← alternatingGroup.kleinFour_eq_commutator (by simp)]
    rfl
  have hVcomm : ∀ x ∈ apm_b97A01_V4, ∀ y ∈ apm_b97A01_V4, x * y = y * x := by
    intro x hx y hy
    rw [apm_b97A01_V4, Subgroup.mem_map] at hx hy
    rcases hx with ⟨x', hx', rfl⟩
    rcases hy with ⟨y', hy', rfl⟩
    letI : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
      alternatingGroup.kleinFour_isKleinFour (by simp)
    let xx : alternatingGroup.kleinFour (Fin 4) := ⟨x', hx'⟩
    let yy : alternatingGroup.kleinFour (Fin 4) := ⟨y', hy'⟩
    have hxy : xx * yy = yy * xx :=
      IsKleinFour.isMulCommutative.is_comm.comm xx yy
    exact congr_arg
      (fun z : alternatingGroup.kleinFour (Fin 4) =>
        (z : apm_b97A01_S4)) hxy
  constructor
  refine ⟨3, le_bot_iff.mp ?_⟩
  rw [derivedSeries_succ]
  refine (Subgroup.commutator_mono h2 h2).trans ?_
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact hVcomm x hx y hy

lemma apm_b97A01_S4_center_eq_bot :
    Subgroup.center apm_b97A01_S4 = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hzcomm : ∀ g : apm_b97A01_S4, g * z = z * g :=
    Subgroup.mem_center_iff.mp hz
  have hntrans : ¬ ∀ g : apm_b97A01_S4,
      g * apm_b97A01_transposition = apm_b97A01_transposition * g := by
    decide
  have hndouble : ¬ ∀ g : apm_b97A01_S4,
      g * apm_b97A01_doubleTransposition = apm_b97A01_doubleTransposition * g := by
    decide
  have hnthree : ¬ ∀ g : apm_b97A01_S4,
      g * apm_b97A01_threeCycle = apm_b97A01_threeCycle * g := by
    decide
  have hnfour : ¬ ∀ g : apm_b97A01_S4,
      g * apm_b97A01_fourCycle = apm_b97A01_fourCycle * g := by
    decide
  have conjugate_eq (r : apm_b97A01_S4) (h : IsConj r z) : r = z := by
    rcases h with ⟨c, hc⟩
    apply mul_left_cancel (a := (c : apm_b97A01_S4))
    rw [hc]
    exact (hzcomm c).symm
  rcases apm_b97A01_conjugacy_exhaustive z with h | h | h | h | h
  · simpa using h.symm
  · have hr : apm_b97A01_transposition = z := conjugate_eq _ h
    subst z
    exact False.elim (hntrans hzcomm)
  · have hr : apm_b97A01_doubleTransposition = z := conjugate_eq _ h
    subst z
    exact False.elim (hndouble hzcomm)
  · have hr : apm_b97A01_threeCycle = z := conjugate_eq _ h
    subst z
    exact False.elim (hnthree hzcomm)
  · have hr : apm_b97A01_fourCycle = z := conjugate_eq _ h
    subst z
    exact False.elim (hnfour hzcomm)

lemma apm_b97A01_SL23_center_ne_bot :
    Subgroup.center apm_b97A01_SL23 ≠ ⊥ := by
  let A : apm_b97A01_SL23 :=
    ⟨Matrix.scalar (Fin 2) (-1 : ZMod 3), by decide⟩
  have hAcenter : A ∈ Subgroup.center apm_b97A01_SL23 := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    exact ⟨-1, by decide, rfl⟩
  have hAne : A ≠ 1 := by
    intro h
    have h00 := congr_arg
      (fun B : apm_b97A01_SL23 => (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 0) h
    simp [A] at h00
    exact (by decide : (-1 : ZMod 3) ≠ 1) h00
  intro hcenter
  rw [hcenter, Subgroup.mem_bot] at hAcenter
  exact hAne hAcenter

lemma apm_b97A01_SL23_not_equiv_S4 :
    ¬Nonempty (apm_b97A01_SL23 ≃* apm_b97A01_S4) := by
  rintro ⟨e⟩
  have hc : Subgroup.center apm_b97A01_SL23 = ⊥ := by
    apply le_antisymm
    · intro z hz
      have hez : e z ∈ Subgroup.center apm_b97A01_S4 := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro g
        obtain ⟨x, rfl⟩ := e.surjective g
        simpa using congr_arg e (hz x)
      rw [apm_b97A01_S4_center_eq_bot, Subgroup.mem_bot] at hez
      rw [Subgroup.mem_bot]
      exact e.injective (hez.trans e.map_one.symm)
    · exact bot_le
  exact apm_b97A01_SL23_center_ne_bot hc

def apm_b97A01_SL23_unipotent : apm_b97A01_SL23 :=
  ⟨!![(1 : ZMod 3), 1; 0, 1], by decide⟩

def apm_b97A01_SL23_lowerUnipotent : apm_b97A01_SL23 :=
  ⟨!![(1 : ZMod 3), 0; 1, 1], by decide⟩

lemma apm_b97A01_SL23_unipotent_order :
    orderOf apm_b97A01_SL23_unipotent = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    decide
  · intro h
    have h01 := congr_arg
      (fun B : apm_b97A01_SL23 => (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) 0 1) h
    simp [apm_b97A01_SL23_unipotent] at h01

lemma apm_b97A01_card_sylow_three_eq_four
    (G : Type) [Group G] [Finite G] (hG : Nat.card G = 24)
    (P : Sylow 3 G) (hP : ¬(P : Subgroup G).Normal) :
    Nat.card (Sylow 3 G) = 4 := by
  let n := Nat.card (Sylow 3 G)
  let i := (P : Subgroup G).index
  have hndvd : n ∣ i := P.card_dvd_index
  have hidvd : i ∣ 24 := by
    simpa [i, hG] using (P : Subgroup G).index_dvd_card
  have hinot : ¬3 ∣ i := by
    exact P.not_dvd_index
  have hnmod : n ≡ 1 [MOD 3] := card_sylow_modEq_one 3 G
  have hnne : n ≠ 1 := by
    intro hn
    letI : Subsingleton (Sylow 3 G) :=
      (Nat.card_eq_one_iff_unique.mp hn).1
    exact hP (Sylow.normal_of_subsingleton P)
  have hndvd24 : n ∣ 24 := hndvd.trans hidvd
  have hnnot : ¬3 ∣ n := fun h ↦ hinot (h.trans hndvd)
  have hnpos : 0 < n := Nat.card_pos
  have hnle : n ≤ 24 := Nat.le_of_dvd (by omega) hndvd24
  change n = 4
  interval_cases n <;> simp_all [Nat.dvd_iff_mod_eq_zero, Nat.ModEq]

lemma apm_b97A01_sylow_three_card
    (G : Type) [Group G] [Finite G] (hG : Nat.card G = 24)
    (P : Sylow 3 G) : Nat.card P = 3 := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
  have hdvd : Nat.card P ∣ 24 := by
    simpa [hG] using P.toSubgroup.card_subgroup_dvd_card
  have hthree : 3 ∣ Nat.card P := P.dvd_card_of_dvd_card (by omega)
  have hle : Nat.card P ≤ 24 := Nat.le_of_dvd (by omega) hdvd
  have hnlt : n < 3 := by
    by_contra h
    have hn3 : 3 ≤ n := by omega
    have hp : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by omega) hn3
    rw [← hn] at hp
    norm_num at hp
    omega
  interval_cases n <;> simp_all [Nat.dvd_iff_mod_eq_zero]

lemma apm_b97A01_sylow_three_index
    (G : Type) [Group G] [Finite G] (hG : Nat.card G = 24)
    (P : Sylow 3 G) : (P : Subgroup G).index = 8 := by
  have hmul := P.toSubgroup.card_mul_index
  rw [apm_b97A01_sylow_three_card G hG P, hG] at hmul
  omega

noncomputable def apm_b97A01_sylowThreeActionHom
    (G : Type) [Group G] [Finite G] (e : Sylow 3 G ≃ Fin 4) :
    G →* apm_b97A01_S4 :=
  e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (Sylow 3 G))

@[simp] lemma apm_b97A01_sylowThreeActionHom_apply
    (G : Type) [Group G] [Finite G] (e : Sylow 3 G ≃ Fin 4)
    (g : G) (Q : Sylow 3 G) :
    apm_b97A01_sylowThreeActionHom G e g (e Q) = e (g • Q) := by
  simp [apm_b97A01_sylowThreeActionHom, Equiv.permCongr_apply,
    MulAction.toPermHom_apply]

lemma apm_b97A01_mem_sylowThreeActionHom_ker
    (G : Type) [Group G] [Finite G] (e : Sylow 3 G ≃ Fin 4)
    (g : G) :
    g ∈ (apm_b97A01_sylowThreeActionHom G e).ker ↔
      ∀ Q : Sylow 3 G, g • Q = Q := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg Q
    apply e.injective
    rw [← apm_b97A01_sylowThreeActionHom_apply]
    simp [hg]
  · intro hg
    apply Equiv.ext
    intro i
    obtain ⟨Q, rfl⟩ := e.surjective i
    simp [hg]

lemma apm_b97A01_three_not_dvd_sylowAction_ker
    (G : Type) [Group G] [Finite G] (hG : Nat.card G = 24)
    (P : Sylow 3 G) (hP : ¬(P : Subgroup G).Normal)
    (e : Sylow 3 G ≃ Fin 4) :
    ¬3 ∣ Nat.card (apm_b97A01_sylowThreeActionHom G e).ker := by
  intro hdvd
  let φ := apm_b97A01_sylowThreeActionHom G e
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime
    (G := φ.ker) 3 (n := 1) (by simpa using hdvd)
  let H : Subgroup G := K.map φ.ker.subtype
  have hHcard : Nat.card H = 3 := by
    rw [show Nat.card H = Nat.card K by
      exact Subgroup.card_subtype φ.ker K]
    simpa using hKcard
  have hHp : IsPGroup 3 H := IsPGroup.of_card (n := 1) (by simpa using hHcard)
  obtain ⟨Q, hHQ⟩ := hHp.exists_le_sylow
  have hQcard : Nat.card Q = 3 := apm_b97A01_sylow_three_card G hG Q
  have hHQeq : H = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hHQ (by rw [hHcard, hQcard])
  have hQker : (Q : Subgroup G) ≤ φ.ker := by
    rw [← hHQeq]
    exact Subgroup.map_subtype_le K
  have hall : ∀ R : Sylow 3 G, R = Q := by
    intro R
    have hfixed : R ∈ MulAction.fixedPoints (Q : Subgroup G) (Sylow 3 G) := by
      intro x
      exact (apm_b97A01_mem_sylowThreeActionHom_ker G e x).mp
        (hQker x.property) R
    have hQR : (Q : Subgroup G) ≤ R :=
      Q.isPGroup'.sylow_mem_fixedPoints_iff.mp hfixed
    exact Sylow.ext (Q.is_maximal' R.isPGroup' hQR)
  letI : Subsingleton (Sylow 3 G) := ⟨fun R S ↦ (hall R).trans (hall S).symm⟩
  have hone : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
  rw [apm_b97A01_card_sylow_three_eq_four G hG P hP] at hone
  omega

lemma apm_b97A01_sylow_three_normalizer_index
    (G : Type) [Group G] [Finite G] (hG : Nat.card G = 24)
    (P : Sylow 3 G) (hP : ¬(P : Subgroup G).Normal) :
    (Subgroup.normalizer (P : Set G)).index = 4 := by
  exact P.card_eq_index_normalizer.symm.trans
    (apm_b97A01_card_sylow_three_eq_four G hG P hP)

set_option maxHeartbeats 2000000 in
lemma apm_b97A01_sylowAction_ker_card
    (G : Type) [Group G] [Finite G] (hG : Nat.card G = 24)
    (hnotiso : ¬Nonempty (G ≃* apm_b97A01_S4))
    (P : Sylow 3 G) (hP : ¬(P : Subgroup G).Normal)
    (e : Sylow 3 G ≃ Fin 4) :
    Nat.card (apm_b97A01_sylowThreeActionHom G e).ker = 2 := by
  let φ : G →* apm_b97A01_S4 := apm_b97A01_sylowThreeActionHom G e
  let K : Subgroup G := φ.ker
  let N : Subgroup G := Subgroup.normalizer ((P : Subgroup G) : Set G)
  have hknot3 : ¬3 ∣ Nat.card K :=
    apm_b97A01_three_not_dvd_sylowAction_ker G hG P hP e
  have hkerle : K ≤ N := by
    intro g hg
    rw [← Sylow.smul_eq_iff_mem_normalizer]
    exact (apm_b97A01_mem_sylowThreeActionHom_ker G e g).mp hg P
  have h4index : 4 ∣ K.index := by
    have hn : N.index = 4 :=
      apm_b97A01_sylow_three_normalizer_index G hG P hP
    calc
      4 = N.index := hn.symm
      _ ∣ K.index := Subgroup.index_dvd_of_le hkerle
  have hmul : Nat.card K * K.index = 24 := by
    simpa [hG] using K.card_mul_index
  have hkpos : 0 < Nat.card K := Nat.card_pos
  have hkdvd : Nat.card K ∣ 24 := by
    simpa [hG] using K.card_subgroup_dvd_card
  have hkle : Nat.card K ≤ 24 := Nat.le_of_dvd (by omega) hkdvd
  have hkne1 : Nat.card K ≠ 1 := by
    intro hk
    have hkbot : K = ⊥ :=
      (Subgroup.card_le_one_iff_eq_bot K).mp (by omega)
    have hinj : Function.Injective φ := φ.ker_eq_bot_iff.mp hkbot
    have hS4card : Nat.card apm_b97A01_S4 = 24 := by
      rw [Nat.card_perm]
      norm_num
    have hbij : Function.Bijective φ :=
      hinj.bijective_of_nat_card_le (by rw [hG, hS4card])
    exact hnotiso ⟨MulEquiv.ofBijective φ hbij⟩
  let k := Nat.card K
  have hkle' : k ≤ 24 := hkle
  change ¬3 ∣ k at hknot3
  change k * K.index = 24 at hmul
  change k ≠ 1 at hkne1
  rcases h4index with ⟨c, hc⟩
  change Nat.card (apm_b97A01_sylowThreeActionHom G e).ker = 2
  change k = 2
  interval_cases k <;> first | omega | (exfalso; apply hknot3; norm_num)

/-- Why this unblocks `apm_b97a01`: this is the universal order-24 action
theorem isolated from the concrete `SL₂(F₃)` example. A nonnormal Sylow
3-subgroup in a group not isomorphic to `S₄` yields the stated quotient map
and forces a normal Sylow 2-subgroup. -/
theorem apm_b97A01_bridge_order24_action :
    ∀ (G : Type) [Group G] [Finite G],
      Nat.card G = 24 →
      ¬Nonempty (G ≃* apm_b97A01_S4) →
      ∀ P3 : Sylow 3 G, ¬(P3 : Subgroup G).Normal →
        ∃ phi : G →* apm_b97A01_S4,
          Nat.card phi.ker = 2 ∧
          ∃ P2 : Sylow 2 G, (P2 : Subgroup G).Normal := by
  intro G _ _ hG hnotiso P3 hP3
  have hsylowCard : Nat.card (Sylow 3 G) = 4 :=
    apm_b97A01_card_sylow_three_eq_four G hG P3 hP3
  let e : Sylow 3 G ≃ Fin 4 := Finite.equivFinOfCardEq hsylowCard
  let φ : G →* apm_b97A01_S4 := apm_b97A01_sylowThreeActionHom G e
  have hker : Nat.card φ.ker = 2 :=
    apm_b97A01_sylowAction_ker_card G hG hnotiso P3 hP3 e
  have hS4card : Nat.card apm_b97A01_S4 = 24 := by
    rw [Nat.card_perm]
    norm_num
  have hrangeCard : Nat.card φ.range = 12 := by
    have hm := φ.ker.card_mul_index
    rw [Subgroup.index_ker] at hm
    rw [hker, hG] at hm
    omega
  have hrangeIndex : φ.range.index = 2 := by
    have hm := φ.range.card_mul_index
    rw [hrangeCard, hS4card] at hm
    omega
  have hrange : φ.range = alternatingGroup (Fin 4) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hrangeIndex
  have hV4range : apm_b97A01_V4 ≤ φ.range := by
    rw [hrange]
    unfold apm_b97A01_V4
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hkerP : IsPGroup 2 φ.ker :=
    IsPGroup.of_card (n := 1) (by simpa using hker)
  have hV4P : IsPGroup 2 apm_b97A01_V4 :=
    IsPGroup.of_card (n := 2) (by simpa using apm_b97A01_V4_card)
  have hV4index : apm_b97A01_V4.index = 6 := by
    have hm := apm_b97A01_V4.card_mul_index
    rw [apm_b97A01_V4_card, hS4card] at hm
    omega
  let H : Subgroup G := apm_b97A01_V4.comap φ
  have hHP : IsPGroup 2 H := hV4P.comap_of_ker_isPGroup φ hkerP
  have hHindex : H.index = 3 := by
    rw [Subgroup.index_comap]
    have hm := Subgroup.relIndex_mul_index hV4range
    rw [hV4index, hrangeIndex] at hm
    omega
  let P2 : Sylow 2 G := hHP.toSylow (by rw [hHindex]; norm_num)
  refine ⟨φ, hker, P2, ?_⟩
  change (apm_b97A01_V4.comap φ).Normal
  exact apm_b97A01_V4_normal.comap φ

/-- Why this unblocks `apm_b97a01`: these are the two remaining structural
facts about the literal matrix group `SL₂(F₃)`. Its center distinguishes it
from `S₄`, and its Sylow-3 subgroups are not normal. -/
theorem apm_b97A01_bridge_SL23_structure :
    ¬Nonempty (apm_b97A01_SL23 ≃* apm_b97A01_S4) ∧
    ∃ P3 : Sylow 3 apm_b97A01_SL23,
      ¬(P3 : Subgroup apm_b97A01_SL23).Normal := by
  refine ⟨apm_b97A01_SL23_not_equiv_S4, ?_⟩
  let H : Subgroup apm_b97A01_SL23 :=
    Subgroup.zpowers apm_b97A01_SL23_unipotent
  have hHcard : Nat.card H = 3 := by
    change Nat.card (Subgroup.zpowers apm_b97A01_SL23_unipotent) = _
    rw [Nat.card_zpowers, apm_b97A01_SL23_unipotent_order]
  have hHp : IsPGroup 3 H := by
    apply IsPGroup.of_card (n := 1)
    simpa using hHcard
  have hHindex : H.index = 8 := by
    have hcardindex := H.card_mul_index
    rw [hHcard, apm_b97A01_SL23_card] at hcardindex
    omega
  have hindex : ¬3 ∣ H.index := by rw [hHindex]; decide
  let P : Sylow 3 apm_b97A01_SL23 := hHp.toSylow hindex
  refine ⟨P, ?_⟩
  intro hnormal
  have hu : apm_b97A01_SL23_unipotent ∈ (P : Subgroup apm_b97A01_SL23) := by
    change apm_b97A01_SL23_unipotent ∈ H
    exact Subgroup.mem_zpowers _
  have hc := hnormal.conj_mem apm_b97A01_SL23_unipotent hu
    apm_b97A01_SL23_lowerUnipotent
  change apm_b97A01_SL23_lowerUnipotent * apm_b97A01_SL23_unipotent *
      apm_b97A01_SL23_lowerUnipotent⁻¹ ∈ H at hc
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,
    apm_b97A01_SL23_unipotent_order] at hc
  rcases Finset.mem_image.mp hc with ⟨n, hn, heq⟩
  have hnlt : n < 3 := Finset.mem_range.mp hn
  interval_cases n <;>
    have heq' := congr_arg
      (fun B : apm_b97A01_SL23 => (B : Matrix (Fin 2) (Fin 2) (ZMod 3)) 1 0) heq <;>
    simp [apm_b97A01_SL23_unipotent,
      apm_b97A01_SL23_lowerUnipotent, Matrix.mul_apply,
      Fin.sum_univ_two, pow_two] at heq'

theorem apm_b97a01 :
    (∀ σ : apm_b97A01_S4,
      (IsConj 1 σ ↔ σ.cycleType = {}) ∧
      (IsConj apm_b97A01_transposition σ ↔ σ.cycleType = {2}) ∧
      (IsConj apm_b97A01_doubleTransposition σ ↔
        σ.cycleType = {2, 2}) ∧
      (IsConj apm_b97A01_threeCycle σ ↔ σ.cycleType = {3}) ∧
      (IsConj apm_b97A01_fourCycle σ ↔ σ.cycleType = {4}) ∧
      (IsConj 1 σ ∨ IsConj apm_b97A01_transposition σ ∨
        IsConj apm_b97A01_doubleTransposition σ ∨
        IsConj apm_b97A01_threeCycle σ ∨
        IsConj apm_b97A01_fourCycle σ)) ∧
    Nat.card {σ : apm_b97A01_S4 // IsConj 1 σ} = 1 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_transposition σ} = 6 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_doubleTransposition σ} = 3 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_threeCycle σ} = 8 ∧
    Nat.card
      {σ : apm_b97A01_S4 // IsConj apm_b97A01_fourCycle σ} = 6 ∧
    (∀ N : Subgroup apm_b97A01_S4,
      N.Normal ↔
        N = ⊥ ∨ N = apm_b97A01_V4 ∨
        N = alternatingGroup (Fin 4) ∨ N = ⊤) ∧
    IsSolvable apm_b97A01_S4 ∧
    (∀ (G : Type) [Group G] [Finite G],
      Nat.card G = 24 →
      ¬Nonempty (G ≃* apm_b97A01_S4) →
      ∀ P3 : Sylow 3 G, ¬(P3 : Subgroup G).Normal →
        ∃ φ : G →* apm_b97A01_S4,
          Nat.card φ.ker = 2 ∧
          ∃ P2 : Sylow 2 G, (P2 : Subgroup G).Normal) ∧
    Nat.card apm_b97A01_SL23 = 24 ∧
    ¬Nonempty (apm_b97A01_SL23 ≃* apm_b97A01_S4) ∧
    ∃ P3 : Sylow 3 apm_b97A01_SL23,
      ¬(P3 : Subgroup apm_b97A01_SL23).Normal := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib's
  `Equiv.Perm.isConj_iff_cycleType_eq` supplies the abstract conjugacy-class
  criterion, but searches of the local Mathlib sources and solved sibling
  artifacts found no packaged bridge for the exhaustive `Fin 4` cycle-type
  enumeration and class cardinalities, the full normal-subgroup lattice of
  `Equiv.Perm (Fin 4)`, the universal order-24 action theorem, or the concrete
  cardinality and Sylow facts for `SpecialLinearGroup (Fin 2) (ZMod 3)`.
  Closer hop 1 compiles two concrete bridges that the original search left
  open. `apm_b97A01_SL23_card` rewrites `Nat.card` to the concrete `Fintype`
  cardinality and verifies that `SL₂(ZMod 3)` has order 24.
  `apm_b97A01_representative_cycleTypes` verifies the advertised cycle types
  of all four nonidentity representatives; together with
  `Equiv.Perm.isConj_iff_cycleType_eq`, this removes the representative side of
  the first five equivalences.

  I additionally tested direct finite decision for the existence of a
  nonnormal Sylow subgroup and center-cardinality separation from `S₄`.
  `Sylow` existence/normality has no computable `Decidable` instance, while
  subgroup-center `Fintype.ofFinite` is noncomputable, so neither test yields a
  kernel-compilable proof. These latter clauses are not reducible by a single finite computation: the
  theorem quantifies over arbitrary finite groups of order 24, and its
  `Nat.card`/subgroup assertions require structural group-theoretic proofs.
  Renewed searches of `LEMMA-INDEX.md`, the closed corpus,
  `ConstructionTargets/`, and the special-linear-group source found no
  structural replacement. The statement appears mathematically
  sound; the blocker is the missing formal API/bridge, not a counterexample.

  Closer hop 2 goes beyond the finite-decision attempt by using Mathlib's
  structural permutation API. `apm_b97A01_conjugacy_classification` applies
  `Equiv.Perm.isConj_iff_cycleType_eq` to the compiled representative cycle
  types, proving the first five class-characterization equivalences.
  `apm_b97A01_conjugacy_class_cards` applies the centralizer formula
  `Equiv.Perm.card_isConj_eq` and closes all five advertised class
  cardinalities. The exhaustive cycle-type disjunction, normal-subgroup
  lattice, solvability, universal order-24 action theorem, and the two
  structural `SL₂(F₃)` clauses remain open; searches of the solvable-group,
  Sylow, and special-linear APIs found no packaged result closing them.

  Closer hop 3 closes the exhaustive cycle-type disjunction with
  `apm_b97A01_conjugacy_exhaustive` and packages the entire first frozen
  conjunct as `apm_b97A01_complete_conjugacy_classification`.  This finite
  computation is nontrivial—it checks all permutations of `Fin 4` against the
  five concrete conjugacy predicates—and complements the structural
  cycle-type equivalences from hop 2.  The normal-subgroup lattice,
  solvability, universal order-24 theorem, and structural `SL₂(F₃)` clauses
  remain open.
  -/
  rcases apm_b97A01_conjugacy_class_cards with ⟨hcard1, hcard2, hcard22,
    hcard3, hcard4⟩
  refine ⟨apm_b97A01_complete_conjugacy_classification,
    hcard1, hcard2, hcard22, hcard3, hcard4, ?_⟩
  rcases apm_b97A01_bridge_SL23_structure with ⟨hSLne, hSLsylow⟩
  exact ⟨apm_b97A01_bridge_normal_subgroups,
    apm_b97A01_bridge_S4_solvable,
    apm_b97A01_bridge_order24_action,
    apm_b97A01_SL23_card,
    hSLne,
    hSLsylow⟩
