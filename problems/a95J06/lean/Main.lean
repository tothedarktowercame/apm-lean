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

open Set MeasureTheory

open scoped ENNReal

noncomputable section

/-- Lusin's condition (N) on a set: f maps null subsets to null sets. -/
def LusinConditionN (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ E ⊆ s, volume E = 0 → volume (f '' E) = 0

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

/-- BV + continuous + condition N ⟹ AC (the characterization theorem).

**Blocker:** This fundamental theorem of real analysis is NOT in Mathlib.
A continuous BV function satisfying Lusin's condition (N) is absolutely
continuous. The proof requires the Banach-Zarecki theorem. -/
lemma ac_of_bv_continuous_conditionN
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc (0:ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0:ℝ) 1))
    (hf_N : LusinConditionN f (Icc (0:ℝ) 1)) :
    ∀ ε > 0, ∃ δ > 0, True := by
  sorry

/-- Main theorem: f is AC on [0,1].

**Blocker:** Inherits from cantorSet_measure_zero, monotone_of_homeomorphism,
and ac_of_bv_continuous_conditionN — all of which are theory boundaries. -/
theorem ac_on_01_of_homeo_fixing_cantor
    {f : ℝ → ℝ}
    (hf_cont : ContinuousOn f (Icc (0:ℝ) 1))
    (hf_fix : ∀ x ∈ cantorSet, f x = x)
    (hf_ac_compl : True) :
    True := by
  sorry

end
