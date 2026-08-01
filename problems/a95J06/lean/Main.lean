/-
! # APM a95J06: Homeomorphism fixing Cantor set, AC on complement, is AC on [0,1]

C = Cantor set ⊂ [0,1], f : [0,1] → [0,1] homeomorphism with f(x) = x on C,
f AC on every closed interval in [0,1] \ C. Prove f is AC on [0,1].

## Proof strategy

1. f is monotone (continuous bijection on [0,1] ⟹ strictly monotone) ⟹ BV.
2. f = id on C ⟹ condition N on C (trivially, since m(C) = 0).
3. AC on complement ⟹ condition N on [0,1] \ C.
4. Condition N on C ∪ ([0,1]\C) = [0,1] ⟹ global condition N.
5. BV + continuous + condition N ⟹ AC (characterization theorem).

## Theory boundaries

- The Cantor set IS in Mathlib (`Mathlib.Topology.Instances.CantorSet`),
  and its self-similarity equation gives a short proof that its measure is zero.
- The BV + condition N ⟹ AC characterization is NOT in Mathlib.
- `MonotoneOn` / `AntitoneOn` for continuous bijections on intervals IS available.
- The standard middle-thirds Cantor set definition (`cantorSet`) IS available.

## Statement repair

The generated `cantorSet` used `sorry` in its def. We use Mathlib's existing
`cantorSet` from `Mathlib.Topology.Instances.CantorSet`. The generated
`AbsolutelyContinuousOn` definition is correct but verbose; we use a simpler
form matching the standard ε-δ definition.
-/

import Mathlib.Topology.Instances.CantorSet
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import ConstructionTargets.BanachZarecki

open Set MeasureTheory

open scoped ENNReal

noncomputable section

/-- Lusin's condition (N) on a set: f maps null subsets to null sets. -/
def LusinConditionN (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ E ⊆ s, volume E = 0 → volume (f '' E) = 0

namespace LusinConditionN

/-- Condition (N) restricts to subsets of its domain. -/
lemma mono {f : ℝ → ℝ} {s t : Set ℝ} (h : LusinConditionN f s) (hts : t ⊆ s) :
    LusinConditionN f t := by
  intro E hEt hE
  exact h E (hEt.trans hts) hE

/-- Condition (N) is preserved by countable unions of domains. -/
lemma iUnion {f : ℝ → ℝ} {s : ℕ → Set ℝ} (h : ∀ n, LusinConditionN f (s n)) :
    LusinConditionN f (⋃ n, s n) := by
  intro E hE hE_null
  have hsplit : E = ⋃ n, E ∩ s n := by
    ext x
    constructor
    · intro hx
      obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp (hE hx)
      exact Set.mem_iUnion.mpr ⟨n, hx, hxn⟩
    · rintro hx
      obtain ⟨n, hxE, -⟩ := Set.mem_iUnion.mp hx
      exact hxE
  rw [hsplit, image_iUnion]
  apply measure_iUnion_null
  intro n
  apply h n (E ∩ s n) inter_subset_right
  exact measure_mono_null inter_subset_left hE_null

/-- Condition (N) is preserved by a union of two domains. -/
lemma union {f : ℝ → ℝ} {s t : Set ℝ}
    (hs : LusinConditionN f s) (ht : LusinConditionN f t) :
    LusinConditionN f (s ∪ t) := by
  intro E hE hE_null
  have hs_null : volume (E ∩ s) = 0 :=
    measure_mono_null inter_subset_left hE_null
  have ht_null : volume (E ∩ t) = 0 :=
    measure_mono_null inter_subset_left hE_null
  have hfs := hs (E ∩ s) inter_subset_right hs_null
  have hft := ht (E ∩ t) inter_subset_right ht_null
  rw [show E = (E ∩ s) ∪ (E ∩ t) by
    ext x
    constructor
    · intro hx
      rcases hE hx with hxs | hxt
      · exact Or.inl ⟨hx, hxs⟩
      · exact Or.inr ⟨hx, hxt⟩
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx, image_union]
  exact measure_union_null hfs hft

end LusinConditionN

/-- The Cantor set has Lebesgue measure zero.

Use `cantorSet_eq_union_halves`: both pieces have one third the measure of the original set,
so finiteness and `m(C) ≤ 2m(C)/3` force `m(C) = 0`. -/
lemma cantorSet_measure_zero : volume cantorSet = 0 := by
  have hscale :
      volume ((fun x : ℝ => x / 3) '' cantorSet) =
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    rw [show (fun x : ℝ => x / 3) = fun x => (3 : ℝ)⁻¹ * x by funext x; ring,
      show (fun x : ℝ => 3⁻¹ * x) '' cantorSet =
          (fun x : ℝ => 3 * x) ⁻¹' cantorSet by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          simpa using hy
        · intro hx
          exact ⟨3 * x, hx, by ring⟩,
      Real.volume_preimage_mul_left (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  have htranslate :
      volume ((fun x : ℝ => (2 + x) / 3) '' cantorSet) =
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    have himage :
        (fun x : ℝ => (2 + x) / 3) '' cantorSet =
          (fun x : ℝ => 2 / 3 + x) '' ((fun x : ℝ => x / 3) '' cantorSet) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y / 3, ⟨y, hy, rfl⟩, by ring⟩
      · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
        exact ⟨y, hy, by ring⟩
    rw [himage, image_add_left, measure_preimage_add, hscale]
  have hle : volume cantorSet ≤
      ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet +
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet := by
    calc
      volume cantorSet = volume ((fun x : ℝ => x / 3) '' cantorSet ∪
          (fun x : ℝ => (2 + x) / 3) '' cantorSet) :=
        congrArg volume cantorSet_eq_union_halves
      _ ≤ volume ((fun x : ℝ => x / 3) '' cantorSet) +
            volume ((fun x : ℝ => (2 + x) / 3) '' cantorSet) := measure_union_le _ _
      _ = _ := by rw [hscale, htranslate]
  have hfin : volume cantorSet ≠ ∞ := by
    exact ne_of_lt ((measure_mono cantorSet_subset_unitInterval).trans_lt (by simp))
  have hzreal : (volume cantorSet).toReal = 0 := by
    have hmul : ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have hrhs : ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet +
        ENNReal.ofReal (1 / 3 : ℝ) * volume cantorSet ≠ ∞ := by
      exact ENNReal.add_ne_top.mpr ⟨hmul, hmul⟩
    have hreal := ENNReal.toReal_mono hrhs hle
    rw [ENNReal.toReal_add hmul hmul] at hreal
    simp only [ENNReal.toReal_mul] at hreal
    norm_num at hreal
    have hnonneg : 0 ≤ (volume cantorSet).toReal := ENNReal.toReal_nonneg
    apply le_antisymm _ hnonneg
    linarith
  rcases (ENNReal.toReal_eq_zero_iff _).mp hzreal with hzero | htop
  · exact hzero
  · exact (hfin htop).elim

/-- f = id on C implies condition N on C.

Since f(x) = x for x ∈ C: f '' E = E for E ⊆ C. So volume(f '' E) = volume(E) = 0. -/
lemma conditionN_on_cantor_of_fix
    {f : ℝ → ℝ} (hf_fix : ∀ x ∈ cantorSet, f x = x) :
    LusinConditionN f cantorSet := by
  intro E hE hE_null
  -- f '' E = E since f = id on C ⊇ E
  have h_image : f '' E = E := by
    ext y
    constructor
    · rintro ⟨x, hx, hfx⟩
      have : f x = x := hf_fix x (hE hx)
      rw [this] at hfx
      exact hfx ▸ hx
    · intro hy
      exact ⟨y, hy, hf_fix y (hE hy)⟩
  rw [h_image, hE_null]

/-- Every point of an open subset of `ℝ` lies in a rational closed interval
contained in that open set.  This gives a countable family of compact
intervals for local-to-global null-image arguments. -/
lemma exists_rat_Icc_subset_of_mem_open
    {U : Set ℝ} (hU : IsOpen U) {x : ℝ} (hx : x ∈ U) :
    ∃ a b : ℚ, x ∈ Icc (a : ℝ) (b : ℝ) ∧ Icc (a : ℝ) (b : ℝ) ⊆ U := by
  rcases Metric.isOpen_iff.mp hU x hx with ⟨ε, hε, hball⟩
  obtain ⟨a, hxa, hax⟩ := exists_rat_btwn (sub_lt_self x hε)
  obtain ⟨b, hxb, hbx⟩ := exists_rat_btwn (lt_add_of_pos_right x hε)
  refine ⟨a, b, ⟨hax.le, hxb.le⟩, ?_⟩
  intro z hz
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [hxa, hbx, hz.1, hz.2]

/-- A continuous bijection [0,1] → [0,1] is monotone.

This is the standard theorem that a continuous injection on a real interval is strictly
monotone or strictly antitone. -/
lemma monotone_of_homeomorphism
    {f : ℝ → ℝ}
    (hf_bij : BijOn f (Icc 0 1) (Icc 0 1))
    (hf_cont : ContinuousOn f (Icc 0 1)) :
    MonotoneOn f (Icc 0 1) ∨ AntitoneOn f (Icc 0 1) := by
  exact (hf_cont.strictMonoOn_of_injOn_Icc' (by norm_num) hf_bij.injOn).imp
    StrictMonoOn.monotoneOn StrictAntiOn.antitoneOn

/-- A homeomorphism of the unit interval that fixes the Cantor set has the
increasing, rather than decreasing, orientation.  It is enough to compare the
two fixed Cantor points `0` and `1 / 4`. -/
lemma monotone_of_homeomorphism_fixing_cantor
    {f : ℝ → ℝ}
    (hf_bij : BijOn f (Icc 0 1) (Icc 0 1))
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_fix : ∀ x ∈ cantorSet, f x = x) :
    MonotoneOn f (Icc 0 1) := by
  rcases monotone_of_homeomorphism hf_bij hf_cont with hf_mono | hf_anti
  · exact hf_mono
  · exfalso
    have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
    have hquarter : (1 / 4 : ℝ) ∈ Icc 0 1 :=
      cantorSet_subset_unitInterval quarter_mem_cantorSet
    have hle := hf_anti h0 hquarter (by norm_num)
    rw [hf_fix 0 zero_mem_cantorSet, hf_fix (1 / 4) quarter_mem_cantorSet] at hle
    norm_num at hle

/-- The monotone Banach--Zarecki theorem, supplied by the shared construction
target.  Its proof uses a generalized-inverse representation of the
Lebesgue--Stieltjes measure, followed by Radon--Nikodym. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): replace the vacuous
-- epsilon-delta conclusion ending in `True` by Mathlib's absolute-continuity
-- predicate on the unit interval.
lemma ac_of_bv_continuous_conditionN
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc (0:ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0:ℝ) 1))
    (hf_N : LusinConditionN f (Icc (0:ℝ) 1)) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  exact ConstructionTargets.BanachZarecki.banachZarecki_monotone
    hf_cont hf_mono hf_N

/-- Main theorem: f is AC on [0,1]. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): restore the homeomorphism
-- bijection, local absolute-continuity hypothesis, and global
-- absolute-continuity conclusion that the informal problem states.
theorem ac_on_01_of_homeo_fixing_cantor
    {f : ℝ → ℝ}
    (hf_bij : BijOn f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hf_cont : ContinuousOn f (Icc (0:ℝ) 1))
    (hf_fix : ∀ x ∈ cantorSet, f x = x)
    (hf_ac_compl : ∀ a b : ℝ,
      Icc a b ⊆ Icc (0 : ℝ) 1 → Icc a b ⊆ cantorSetᶜ →
      AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  classical
  have hf_mono : MonotoneOn f (Icc (0 : ℝ) 1) :=
    monotone_of_homeomorphism_fixing_cantor hf_bij hf_cont hf_fix
  have hf_N_cantor : LusinConditionN f cantorSet :=
    conditionN_on_cantor_of_fix hf_fix
  -- Cover the open Cantor complement by countably many rational closed
  -- intervals.  Absolute continuity on each interval maps its null subsets to
  -- null sets, and `LusinConditionN.iUnion` combines the resulting claims.
  have hf_N_compl : LusinConditionN f (Icc (0 : ℝ) 1 ∩ cantorSetᶜ) := by
    have hone_pre : ∀ n : ℕ, (1 : ℝ) ∈ preCantorSet n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => exact Or.inr ⟨1, ih, by norm_num⟩
    have hone : (1 : ℝ) ∈ cantorSet := by
      exact mem_iInter.2 hone_pre
    let U : Set ℝ := Ioo (0 : ℝ) 1 ∩ cantorSetᶜ
    have hUopen : IsOpen U := isOpen_Ioo.inter isClosed_cantorSet.isOpen_compl
    let S : ℕ → Set ℝ := fun n =>
      match (Encodable.decode n : Option (ℚ × ℚ)) with
      | none => ∅
      | some p =>
          if Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ U then
            Icc (p.1 : ℝ) (p.2 : ℝ)
          else ∅
    have hSsub : ∀ n, S n ⊆ U := by
      intro n
      change (match (Encodable.decode n : Option (ℚ × ℚ)) with
        | none => ∅
        | some p => if Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ U then
            Icc (p.1 : ℝ) (p.2 : ℝ) else ∅) ⊆ U
      generalize hq : (Encodable.decode n : Option (ℚ × ℚ)) = q
      cases q with
      | none => simp
      | some p =>
        dsimp only
        split_ifs with hp
        · exact hp
        · simp
    have hSN : ∀ n, LusinConditionN f (S n) := by
      intro n
      change LusinConditionN f (match (Encodable.decode n : Option (ℚ × ℚ)) with
        | none => ∅
        | some p => if Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ U then
            Icc (p.1 : ℝ) (p.2 : ℝ) else ∅)
      generalize hq : (Encodable.decode n : Option (ℚ × ℚ)) = q
      cases q with
      | none => simp [LusinConditionN]
      | some p =>
        dsimp only
        split_ifs with hp
        · by_cases hab : (p.1 : ℝ) ≤ (p.2 : ℝ)
          · have haU : (p.1 : ℝ) ∈ U := hp ⟨le_rfl, hab⟩
            have hbU : (p.2 : ℝ) ∈ U := hp ⟨hab, le_rfl⟩
            have hac := hf_ac_compl (p.1 : ℝ) (p.2 : ℝ)
              (fun x hx => ⟨(hp hx).1.1.le, (hp hx).1.2.le⟩)
              (fun x hx => (hp hx).2)
            intro E hE hE0
            exact ConstructionTargets.LusinN.absolutelyContinuousOnInterval_maps_null_to_null
              ⟨haU.1.1.le, haU.1.2.le⟩ ⟨hbU.1.1.le, hbU.1.2.le⟩ hab
              hac hE hE0
          · rw [Icc_eq_empty hab]
            simp [LusinConditionN]
        · simp [LusinConditionN]
    have hcover : ⋃ n, S n = Icc (0 : ℝ) 1 ∩ cantorSetᶜ := by
      apply Subset.antisymm
      · rw [iUnion_subset_iff]
        intro n
        exact (hSsub n).trans fun _ hx => ⟨⟨hx.1.1.le, hx.1.2.le⟩, hx.2⟩
      · intro x hx
        have hx0 : x ≠ 0 := fun h => hx.2 (h ▸ zero_mem_cantorSet)
        have hx1 : x ≠ 1 := fun h => hx.2 (h ▸ hone)
        have hxU : x ∈ U := ⟨⟨lt_of_le_of_ne hx.1.1 (Ne.symm hx0),
          lt_of_le_of_ne hx.1.2 hx1⟩, hx.2⟩
        obtain ⟨a, b, hxab, habU⟩ := exists_rat_Icc_subset_of_mem_open hUopen hxU
        apply mem_iUnion.2
        refine ⟨Encodable.encode (a, b), ?_⟩
        simp [S, Encodable.encodek, habU, hxab]
    rw [← hcover]
    exact LusinConditionN.iUnion hSN
  apply ac_of_bv_continuous_conditionN hf_cont hf_mono
  apply (hf_N_cantor.union hf_N_compl).mono
  intro x hx
  by_cases hxc : x ∈ cantorSet
  · exact Or.inl hxc
  · exact Or.inr ⟨hx, hxc⟩

end
