import Mathlib

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace A02J04FullStep1

def triangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ 1}

def triWeight : ℝ × ℝ → ℝ≥0∞ :=
  triangle.indicator (fun _ => (2 : ℝ≥0∞))

def μ : Measure (ℝ × ℝ) :=
  (volume.prod volume).withDensity triWeight

def τ : Measure ℝ :=
  μ.fst

def tauDensity : ℝ → ℝ≥0∞ :=
  Set.indicator (Set.Icc (0 : ℝ) 1) (fun x => ENNReal.ofReal (2 * x))

lemma triWeight_measurable : Measurable triWeight := by
  refine Measurable.indicator ?_ measurable_const
  simpa [triangle] using
    ((measurable_const.le measurable_snd).and
      ((measurable_snd.le measurable_fst).and (measurable_fst.le measurable_const)))

lemma section_set_eq (x : ℝ) :
    {y : ℝ | (x, y) ∈ triangle} =
      if x ∈ Set.Icc (0 : ℝ) 1 then Set.Icc (0 : ℝ) x else ∅ := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · ext y
    simp [triangle, hx, hx.1, hx.2, and_left_comm, and_assoc]
  · ext y
    simp [triangle, hx]

lemma section_integral (x : ℝ) :
    ∫⁻ y, triWeight (x, y) ∂volume = tauDensity x := by
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · have hsec : {y : ℝ | (x, y) ∈ triangle} = Set.Icc (0 : ℝ) x := by
      simpa [hx] using section_set_eq x
    rw [tauDensity, if_pos hx]
    rw [triWeight, hsec]
    simp [MeasureTheory.lintegral_indicator, measurableSet_Icc, MeasureTheory.volume_Icc, hx.1]
  · have hsec : {y : ℝ | (x, y) ∈ triangle} = (∅ : Set ℝ) := by
      simpa [hx] using section_set_eq x
    rw [tauDensity, if_neg hx]
    rw [triWeight, hsec]
    simp

lemma fst_withDensity_eq_withDensity_lintegral {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    (((volume.prod volume).withDensity f).fst) =
      volume.withDensity (fun x => ∫⁻ y, f (x, y) ∂volume) := by
  ext s hs
  rw [Measure.fst_apply hs, Measure.withDensity_apply _ (measurable_fst hs)]
  rw [show Prod.fst ⁻¹' s = s ×ˢ (Set.univ : Set ℝ) by ext z; simp]
  rw [MeasureTheory.setLIntegral_prod]
  · rw [Measure.withDensity_apply _ hs]
  · exact ((hf.comp_aemeasurable measurable_fst.aemeasurable).prod_mk measurable_id.aemeasurable)

theorem tau_eq_withDensity :
    τ = volume.withDensity tauDensity := by
  rw [τ, μ]
  calc
    (((volume.prod volume).withDensity triWeight).fst)
        = volume.withDensity (fun x => ∫⁻ y, triWeight (x, y) ∂volume) :=
      fst_withDensity_eq_withDensity_lintegral triWeight_measurable
    _ = volume.withDensity tauDensity := by
      refine Measure.withDensity_congr ?_
      filter_upwards with x
      exact section_integral x

end A02J04FullStep1
