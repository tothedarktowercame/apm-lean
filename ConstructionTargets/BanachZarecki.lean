import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import ConstructionTargets.LusinN

/-!
# Banach--Zarecki infrastructure for monotone functions on `[0,1]`

This file starts the positive Lebesgue--Stieltjes route to Banach--Zarecki.
It packages the monotone continuous extension to the real line and proves the
interval formula for its Stieltjes measure.  The remaining construction target
is the Borel-image comparison needed to turn Lusin condition `(N)` into
absolute continuity of that measure with respect to Lebesgue measure.
-/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace ConstructionTargets.BanachZarecki

/-- Retraction of the real line onto the unit interval. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

lemma clamp01_mem (x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

lemma clamp01_eq_self {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clamp01 x = x := by
  simp [clamp01, hx.1, hx.2]

lemma monotone_clamp01 : Monotone clamp01 := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl hxy)

lemma continuous_clamp01 : Continuous clamp01 := by
  exact continuous_const.max (continuous_const.min continuous_id)

/-- Extend a function on `[0,1]` constantly past both endpoints. -/
def monotoneExtension (f : ℝ → ℝ) (x : ℝ) : ℝ := f (clamp01 x)

lemma monotoneExtension_eq_self (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    monotoneExtension f x = f x := by
  rw [monotoneExtension, clamp01_eq_self hx]

lemma monotone_monotoneExtension {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    Monotone (monotoneExtension f) := by
  intro x y hxy
  exact hf (clamp01_mem x) (clamp01_mem y) (monotone_clamp01 hxy)

lemma continuous_monotoneExtension {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) :
    Continuous (monotoneExtension f) := by
  rw [← continuousOn_univ]
  exact hf.comp continuous_clamp01.continuousOn (fun x _ => clamp01_mem x)

/-- The positive Stieltjes measure associated to the clamped monotone
extension of `f`. -/
noncomputable def stieltjesMeasure (f : ℝ → ℝ)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) : Measure ℝ :=
  (monotone_monotoneExtension hf).stieltjesFunction.measure

lemma stieltjesFunction_monotoneExtension_eq
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (x : ℝ) :
    (monotone_monotoneExtension hf_mono).stieltjesFunction x =
      monotoneExtension f x := by
  rw [Monotone.stieltjesFunction_eq]
  exact (continuous_monotoneExtension hf_cont).continuousAt.continuousWithinAt.rightLim_eq

/-- Workhorse interval formula: on `[0,1]`, the Stieltjes measure has exactly
the increment prescribed by `f`. -/
theorem stieltjesMeasure_Ioc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    stieltjesMeasure f hf_mono (Ioc a b) = ENNReal.ofReal (f b - f a) := by
  rw [stieltjesMeasure, StieltjesFunction.measure_Ioc,
    stieltjesFunction_monotoneExtension_eq hf_cont hf_mono,
    stieltjesFunction_monotoneExtension_eq hf_cont hf_mono,
    monotoneExtension_eq_self f hb, monotoneExtension_eq_self f ha]

/-- A continuous monotone function maps a closed subinterval onto the closed
interval between its endpoint values.  This uses no form of Lusin `(N)`. -/
theorem image_Icc_eq_Icc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a ≤ b) :
    f '' Icc a b = Icc (f a) (f b) := by
  have hab_sub : Icc a b ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.1.trans hx.1, hx.2.trans hb.2⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨hf_mono ha (hab_sub hx) hx.1, hf_mono (hab_sub hx) hb hx.2⟩
  · exact intermediate_value_Icc hab (hf_cont.mono hab_sub)

/-- On interval generators, the Stieltjes mass is exactly the Lebesgue
measure of the corresponding closed image interval.  This is the
continuity-and-monotonicity-only input to the remaining Carathéodory step. -/
theorem stieltjesMeasure_Ioc_eq_volume_image_Icc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hab : a ≤ b) :
    stieltjesMeasure f hf_mono (Ioc a b) = volume (f '' Icc a b) := by
  rw [stieltjesMeasure_Ioc hf_cont hf_mono ha hb,
    image_Icc_eq_Icc hf_cont hf_mono ha hb hab, Real.volume_Icc]

/-- Continuity removes all atoms from the associated Stieltjes measure.  This
is needed when image intervals overlap at endpoint or flat-fiber values. -/
theorem stieltjesMeasure_singleton
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (x : ℝ) :
    stieltjesMeasure f hf_mono {x} = 0 := by
  let S := (monotone_monotoneExtension hf_mono).stieltjesFunction
  have hS : (S : ℝ → ℝ) = monotoneExtension f := by
    funext y
    exact stieltjesFunction_monotoneExtension_eq hf_cont hf_mono y
  rw [stieltjesMeasure, StieltjesFunction.measure_singleton]
  change ENNReal.ofReal (S x - Function.leftLim S x) = 0
  rw [hS]
  rw [(continuous_monotoneExtension hf_cont).continuousAt.continuousWithinAt.leftLim_eq,
    sub_self, ENNReal.ofReal_zero]

/-- The clamped extension is bounded, hence its Stieltjes measure is finite.
This supplies the finiteness input for the eventual Radon--Nikodym step. -/
theorem stieltjesMeasure_isFinite
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :
    IsFiniteMeasure (stieltjesMeasure f hf_mono) := by
  let S := (monotone_monotoneExtension hf_mono).stieltjesFunction
  change IsFiniteMeasure S.measure
  apply S.isFiniteMeasure_of_forall_abs_le
  intro x
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hx := clamp01_mem x
  have hlo : f 0 ≤ monotoneExtension f x := by
    exact hf_mono h0 hx hx.1
  have hhi : monotoneExtension f x ≤ f 1 := by
    exact hf_mono hx h1 hx.2
  change |S x| ≤ max |f 0| |f 1|
  rw [stieltjesFunction_monotoneExtension_eq hf_cont hf_mono]
  exact abs_le_max_abs_abs hlo hhi

/-- The lower generalized inverse of `f` on the unit interval.  Restricting
the defining set to `[0,1]` makes the infimum meaningful also at the bottom
endpoint of the range. -/
noncomputable def lowerQuantile (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  sInf {x | x ∈ Icc (0 : ℝ) 1 ∧ y ≤ f x}

lemma lowerQuantile_mem
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    {y : ℝ} (hy : y ≤ f 1) : lowerQuantile f y ∈ Icc (0 : ℝ) 1 := by
  let A : Set ℝ := {x | x ∈ Icc (0 : ℝ) 1 ∧ y ≤ f x}
  have hA_closed : IsClosed A := by
    simpa [A, Set.ext_iff] using
      hf_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hA_compact : IsCompact A := isCompact_Icc.of_isClosed_subset hA_closed (fun _ hx => hx.1)
  have hA_ne : A.Nonempty := by
    exact ⟨1, by norm_num, hy⟩
  change sInf A ∈ Icc (0 : ℝ) 1
  exact (hA_compact.sInf_mem hA_ne).1

lemma lowerQuantile_maps
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Icc (f 0) (f 1)) :
    f (lowerQuantile f y) = y := by
  let A : Set ℝ := {x | x ∈ Icc (0 : ℝ) 1 ∧ y ≤ f x}
  have hA_closed : IsClosed A := by
    simpa [A, Set.ext_iff] using
      hf_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hA_compact : IsCompact A := isCompact_Icc.of_isClosed_subset hA_closed (fun _ hx => hx.1)
  have hA_ne : A.Nonempty := ⟨1, by norm_num, hy.2⟩
  have hqA : lowerQuantile f y ∈ A := by
    change sInf A ∈ A
    exact hA_compact.sInf_mem hA_ne
  apply le_antisymm
  · by_contra hnot
    have hyq : y < f (lowerQuantile f y) := lt_of_not_ge hnot
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have himage := image_Icc_eq_Icc hf_cont hf_mono h0 hqA.1 hqA.1.1
    have hy_mem : y ∈ Icc (f 0) (f (lowerQuantile f y)) := ⟨hy.1, hyq.le⟩
    obtain ⟨x, hx, hfx⟩ := himage.symm.subset hy_mem
    have hxA : x ∈ A := ⟨⟨hx.1, hx.2.trans hqA.1.2⟩, hfx.ge⟩
    have hqx : lowerQuantile f y ≤ x := by
      change sInf A ≤ x
      exact csInf_le hA_compact.bddBelow hxA
    have hxq : x < lowerQuantile f y := hx.2.lt_of_ne (fun h => hyq.ne (h ▸ hfx).symm)
    exact (not_le_of_gt hxq) hqx
  · exact hqA.2

lemma lowerQuantile_mono
    {f : ℝ → ℝ} {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (hy₂ : y₂ ≤ f 1) :
    lowerQuantile f y₁ ≤ lowerQuantile f y₂ := by
  let A₁ : Set ℝ := {x | x ∈ Icc (0 : ℝ) 1 ∧ y₁ ≤ f x}
  let A₂ : Set ℝ := {x | x ∈ Icc (0 : ℝ) 1 ∧ y₂ ≤ f x}
  have hA₁_bdd : BddBelow A₁ := ⟨0, fun _ hx => hx.1.1⟩
  have hA₂_ne : A₂.Nonempty := ⟨1, by norm_num, hy₂⟩
  change sInf A₁ ≤ sInf A₂
  exact csInf_le_csInf hA₁_bdd hA₂_ne (fun _ hx => ⟨hx.1, hy.trans hx.2⟩)

/-- The generalized inverse, extended constantly outside the value interval. -/
noncomputable def quantile (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  lowerQuantile f (max (f 0) (min (f 1) y))

lemma monotone_quantile
    {f : ℝ → ℝ} (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :
    Monotone (quantile f) := by
  have h01 : f 0 ≤ f 1 := hf_mono (by norm_num) (by norm_num) (by norm_num)
  intro y₁ y₂ hy
  apply lowerQuantile_mono
  · exact max_le_max le_rfl (min_le_min le_rfl hy)
  · exact max_le h01 (min_le_left _ _)

lemma measurable_quantile
    {f : ℝ → ℝ} (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :
    Measurable (quantile f) :=
  (monotone_quantile hf_mono).measurable

lemma quantile_maps
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Icc (f 0) (f 1)) :
    f (quantile f y) = y := by
  rw [quantile, min_eq_right hy.2, max_eq_right hy.1]
  exact lowerQuantile_maps hf_cont hf_mono hy

lemma quantile_mem_unit
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    {y : ℝ} (hy : y ∈ Icc (f 0) (f 1)) :
    quantile f y ∈ Icc (0 : ℝ) 1 := by
  rw [quantile, min_eq_right hy.2, max_eq_right hy.1]
  exact lowerQuantile_mem hf_cont hy.2

lemma quantile_mem_Ioc_iff
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b y : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (f 0) (f 1)) :
    quantile f y ∈ Ioc a b ↔ y ∈ Ioc (f a) (f b) := by
  have hq := quantile_mem_unit hf_cont hy
  have hmap := quantile_maps hf_cont hf_mono hy
  constructor
  · intro h
    constructor
    · by_contra hnot
      have hyfa : y ≤ f a := le_of_not_gt hnot
      have hq_le_a : quantile f y ≤ a := by
        rw [quantile, min_eq_right hy.2, max_eq_right hy.1]
        apply csInf_le
        · exact ⟨0, fun _ hx => hx.1.1⟩
        · exact ⟨ha, hyfa⟩
      exact (not_le_of_gt h.1) hq_le_a
    · simpa [hmap] using hf_mono hq hb h.2
  · intro h
    constructor
    · by_contra hnot
      have hq_le_a : quantile f y ≤ a := le_of_not_gt hnot
      have := hf_mono hq ha hq_le_a
      rw [hmap] at this
      exact (not_le_of_gt h.1) this
    · rw [quantile, min_eq_right hy.2, max_eq_right hy.1]
      apply csInf_le
      · exact ⟨0, fun _ hx => hx.1.1⟩
      · exact ⟨hb, h.2⟩

lemma quantile_le_iff
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a y : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (f 0) (f 1)) :
    quantile f y ≤ a ↔ y ≤ f a := by
  have hq := quantile_mem_unit hf_cont hy
  have hmap := quantile_maps hf_cont hf_mono hy
  constructor
  · intro hqa
    simpa [hmap] using hf_mono hq ha hqa
  · intro hya
    rw [quantile, min_eq_right hy.2, max_eq_right hy.1]
    exact csInf_le ⟨0, fun _ hx => hx.1.1⟩ ⟨ha, hya⟩

lemma range_inter_quantile_preimage_Ioc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    Icc (f 0) (f 1) ∩ quantile f ⁻¹' Ioc a b = Ioc (f a) (f b) := by
  ext y
  constructor
  · rintro ⟨hy, hqy⟩
    exact (quantile_mem_Ioc_iff hf_cont hf_mono ha hb hy).1 hqy
  · intro hy
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hyrange : y ∈ Icc (f 0) (f 1) :=
      ⟨((hf_mono h0 ha ha.1).trans_lt hy.1).le,
        hy.2.trans (hf_mono hb h1 hb.2)⟩
    exact ⟨hyrange, (quantile_mem_Ioc_iff hf_cont hf_mono ha hb hyrange).2 hy⟩

lemma range_inter_quantile_preimage_Iic
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    Icc (f 0) (f 1) ∩ quantile f ⁻¹' Iic a = Icc (f 0) (f a) := by
  ext y
  constructor
  · rintro ⟨hy, hqy⟩
    exact ⟨hy.1, (quantile_le_iff hf_cont hf_mono ha hy).1 hqy⟩
  · intro hy
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
    have hyrange : y ∈ Icc (f 0) (f 1) :=
      ⟨hy.1, hy.2.trans (hf_mono ha h1 ha.2)⟩
    exact ⟨hyrange, (quantile_le_iff hf_cont hf_mono ha hyrange).2 hy.2⟩

/-- Lebesgue measure on the value interval, pushed forward by the generalized
inverse. -/
noncomputable def quantileMeasure (f : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc (f 0) (f 1))).map (quantile f)

theorem quantileMeasure_Ioc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) (hb : b ∈ Icc (0 : ℝ) 1) :
    quantileMeasure f (Ioc a b) = ENNReal.ofReal (f b - f a) := by
  rw [quantileMeasure, Measure.map_apply (measurable_quantile hf_mono) measurableSet_Ioc,
    Measure.restrict_apply (measurableSet_Ioc.preimage (measurable_quantile hf_mono))]
  rw [inter_comm, range_inter_quantile_preimage_Ioc hf_cont hf_mono ha hb,
    Real.volume_Ioc]

theorem quantileMeasure_Iic
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (a : ℝ) :
    quantileMeasure f (Iic a) =
      ENNReal.ofReal (monotoneExtension f a - f 0) := by
  rw [quantileMeasure, Measure.map_apply (measurable_quantile hf_mono) measurableSet_Iic,
    Measure.restrict_apply (measurableSet_Iic.preimage (measurable_quantile hf_mono))]
  by_cases ha0 : a < 0
  · have hempty : Icc (f 0) (f 1) ∩ quantile f ⁻¹' Iic a = ∅ := by
      ext y
      constructor
      · rintro ⟨hy, hqy⟩
        exact (not_le_of_gt (ha0.trans_le (quantile_mem_unit hf_cont hy).1)) hqy
      · simp
    rw [inter_comm, hempty, measure_empty]
    simp [monotoneExtension, clamp01, ha0.le]
  · have ha_nonneg : 0 ≤ a := le_of_not_gt ha0
    by_cases ha1 : a ≤ 1
    · have ha : a ∈ Icc (0 : ℝ) 1 := ⟨ha_nonneg, ha1⟩
      rw [inter_comm, range_inter_quantile_preimage_Iic hf_cont hf_mono ha,
        Real.volume_Icc, monotoneExtension_eq_self f ha]
    · have h1a : 1 < a := lt_of_not_ge ha1
      have hfull : Icc (f 0) (f 1) ∩ quantile f ⁻¹' Iic a = Icc (f 0) (f 1) := by
        ext y
        constructor
        · exact fun h => h.1
        · intro hy
          exact ⟨hy, (quantile_mem_unit hf_cont hy).2.trans h1a.le⟩
      rw [inter_comm, hfull, Real.volume_Icc]
      simp [monotoneExtension, clamp01, h1a.le]

lemma tendsto_monotoneExtension_atBot (f : ℝ → ℝ) :
    Filter.Tendsto (monotoneExtension f) Filter.atBot (nhds (f 0)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_le_atBot (0 : ℝ)] with x hx
  simp [monotoneExtension, clamp01, hx]

theorem stieltjesMeasure_Iic
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) (a : ℝ) :
    stieltjesMeasure f hf_mono (Iic a) =
      ENNReal.ofReal (monotoneExtension f a - f 0) := by
  rw [stieltjesMeasure,
    StieltjesFunction.measure_Iic]
  · rw [stieltjesFunction_monotoneExtension_eq hf_cont hf_mono]
  · exact (tendsto_monotoneExtension_atBot f).congr'
      (Filter.Eventually.of_forall fun x =>
        (stieltjesFunction_monotoneExtension_eq hf_cont hf_mono x).symm)

/-- The Stieltjes measure is the pushforward of Lebesgue measure on the value
interval by the generalized inverse. -/
theorem stieltjesMeasure_eq_quantileMeasure
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :
    stieltjesMeasure f hf_mono = quantileMeasure f := by
  letI : IsFiniteMeasure (stieltjesMeasure f hf_mono) :=
    stieltjesMeasure_isFinite hf_cont hf_mono
  apply Measure.ext_of_Iic
  intro a
  rw [stieltjesMeasure_Iic hf_cont hf_mono, quantileMeasure_Iic hf_cont hf_mono]

/-- The Borel-image comparison required by Banach--Zarecki.  Crucially, this
uses only continuity and monotonicity, not Lusin condition `(N)`. -/
theorem stieltjesMeasure_le_volume_image
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    {E : Set ℝ} (hE : MeasurableSet E) (hE_sub : E ⊆ Icc (0 : ℝ) 1) :
    stieltjesMeasure f hf_mono E ≤ volume (f '' E) := by
  rw [stieltjesMeasure_eq_quantileMeasure hf_cont hf_mono, quantileMeasure,
    Measure.map_apply (measurable_quantile hf_mono) hE,
    Measure.restrict_apply (hE.preimage (measurable_quantile hf_mono))]
  apply measure_mono
  rintro y ⟨hqy, hy⟩
  have _hq_unit := hE_sub hqy
  exact ⟨quantile f y, hqy, quantile_maps hf_cont hf_mono hy⟩

theorem stieltjesMeasure_compl_Icc
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1)) :
    stieltjesMeasure f hf_mono (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [stieltjesMeasure_eq_quantileMeasure hf_cont hf_mono, quantileMeasure,
    Measure.map_apply (measurable_quantile hf_mono) measurableSet_Icc.compl,
    Measure.restrict_apply (measurableSet_Icc.compl.preimage (measurable_quantile hf_mono))]
  have hempty : quantile f ⁻¹' (Icc (0 : ℝ) 1)ᶜ ∩ Icc (f 0) (f 1) = ∅ := by
    ext y
    constructor
    · rintro ⟨hq, hy⟩
      exact (hq (quantile_mem_unit hf_cont hy)).elim
    · simp
  rw [hempty, measure_empty]

theorem stieltjesMeasure_absolutelyContinuous_of_maps_null
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    (hf_N : ∀ E ⊆ Icc (0 : ℝ) 1, volume E = 0 → volume (f '' E) = 0) :
    stieltjesMeasure f hf_mono ≪ volume := by
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hE_null
  let A := E ∩ Icc (0 : ℝ) 1
  have hA_meas : MeasurableSet A := hE.inter measurableSet_Icc
  have hA_sub : A ⊆ Icc (0 : ℝ) 1 := inter_subset_right
  have hA_null : volume A = 0 := measure_mono_null inter_subset_left hE_null
  have himage_null : volume (f '' A) = 0 := hf_N A hA_sub hA_null
  have hμA : stieltjesMeasure f hf_mono A = 0 :=
    nonpos_iff_eq_zero.mp <|
      (stieltjesMeasure_le_volume_image hf_cont hf_mono hA_meas hA_sub).trans_eq himage_null
  have hsupport : ∀ᵐ x ∂(stieltjesMeasure f hf_mono), x ∈ Icc (0 : ℝ) 1 := by
    show Icc (0 : ℝ) 1 ∈ ae (stieltjesMeasure f hf_mono)
    simpa using
      (compl_mem_ae_iff.mpr (stieltjesMeasure_compl_Icc hf_cont hf_mono))
  rw [← Measure.measure_inter_eq_of_ae hsupport]
  simpa [A, inter_comm] using hμA

theorem banachZarecki_monotone
    {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf_mono : MonotoneOn f (Icc (0 : ℝ) 1))
    (hf_N : ∀ E ⊆ Icc (0 : ℝ) 1, volume E = 0 → volume (f '' E) = 0) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  let μ := stieltjesMeasure f hf_mono
  letI : IsFiniteMeasure μ := stieltjesMeasure_isFinite hf_cont hf_mono
  have hμv : μ ≪ volume :=
    stieltjesMeasure_absolutelyContinuous_of_maps_null hf_cont hf_mono hf_N
  let g : ℝ → ℝ := fun x => (μ.rnDeriv volume x).toReal
  have hg_on : IntegrableOn g (Icc (0 : ℝ) 1) volume := by
    apply Measure.integrableOn_toReal_rnDeriv
    exact (measure_lt_top μ (Icc (0 : ℝ) 1)).ne
  have hg : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hg_on
  have hprimitive (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      f x = f 0 + ∫ t in (0 : ℝ)..x, g t := by
    have hrn := Measure.setIntegral_toReal_rnDeriv_eq_withDensity'
      (μ := μ) (ν := volume) (s := Ioc (0 : ℝ) x) measurableSet_Ioc
    rw [Measure.withDensity_rnDeriv_eq _ _ hμv] at hrn
    rw [intervalIntegral.integral_of_le hx.1]
    change f x = f 0 + ∫ t in Ioc (0 : ℝ) x, (μ.rnDeriv volume t).toReal ∂volume
    rw [hrn, measureReal_def]
    dsimp [μ]
    rw [stieltjesMeasure_Ioc hf_cont hf_mono (by norm_num) hx,
      ENNReal.toReal_ofReal]
    · ring
    · exact sub_nonneg.mpr (hf_mono (by norm_num) hx hx.1)
  have hG : AbsolutelyContinuousOnInterval
      (fun x => f 0 + ∫ t in (0 : ℝ)..x, g t) 0 1 := by
    rw [AbsolutelyContinuousOnInterval]
    simpa only [dist_add_left] using
      (hg.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp))
  rw [AbsolutelyContinuousOnInterval] at hG ⊢
  apply hG.congr'
  filter_upwards [Filter.mem_inf_of_right
      (Filter.mem_principal_self (AbsolutelyContinuousOnInterval.disjWithin 0 1))] with E hE
  apply Finset.sum_congr rfl
  intro i hi
  have hends := hE.1 i hi
  rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hends
  rw [hprimitive (E.2 i).1 hends.1, hprimitive (E.2 i).2 hends.2]

/-!
## Completed construction

The generalized inverse identifies the Stieltjes measure with the pushforward
of Lebesgue measure on the value interval.  This gives the Borel-image
comparison from continuity and monotonicity alone.  Lusin `(N)` is applied
only afterwards to obtain measure domination.  Radon--Nikodym then represents
`f - f 0` as an interval-integral primitive, completing the monotone
Banach--Zarecki theorem.
-/

end ConstructionTargets.BanachZarecki
