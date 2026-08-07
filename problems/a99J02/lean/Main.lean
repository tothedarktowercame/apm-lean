import Mathlib

open Filter MeasureTheory Set Topology ENNReal
open scoped Pointwise Topology Convolution symmDiff ENNReal

noncomputable section

/-!
# APM a99J02

## Statement repairs

The source's `E \leq [0,1]` is read as the intended set containment
`E \subseteq [0,1]`; numerical order between a set and an interval is ill-typed.

## Encoding notes

`apmTranslate E t` is exactly the image `{x+t | x ∈ E}`, and
`apmIndicatorConvolution` is the displayed Lebesgue integral on all of `ℝ`.
-/

def apmIndicator (E : Set ℝ) : ℝ → ℝ :=
  E.indicator (fun _ ↦ 1)

noncomputable def apmIndicatorConvolution (E : Set ℝ) (x : ℝ) : ℝ :=
  ∫ y, apmIndicator E (x - y) * apmIndicator E y ∂volume

def apmTranslate (E : Set ℝ) (t : ℝ) : Set ℝ :=
  (fun x ↦ x + t) '' E

lemma apmIndicator_memLp_two
    {E : Set ℝ} (hE : MeasurableSet E) (hEfin : volume E ≠ ⊤) :
    MemLp (apmIndicator E) 2 volume := by
  simpa [apmIndicator] using
    memLp_indicator_const (2 : ENNReal) hE (1 : ℝ) (Or.inr hEfin)

lemma apm_exists_ball_subset_sub
    {E : Set ℝ} (hE : MeasurableSet E) (hEpos : 0 < volume E) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → t ∈ E - E := by
  have hnhds : E - E ∈ 𝓝 (0 : ℝ) :=
    MeasureTheory.Measure.sub_mem_nhds_zero_of_addHaar_pos volume E hE hEpos
  rcases Metric.mem_nhds_iff.1 hnhds with ⟨ε, hε, hball⟩
  refine ⟨ε, hε, ?_⟩
  intro t ht
  exact hball (by simpa [Real.dist_eq] using ht)

/- The measured-set continuity argument is adapted from the closed sibling
`a96J02`.  Using the reflected set `-E` below converts its subtraction
orientation `t - y ∈ -E` into the image-translate orientation `y ∈ E + t`
used in this problem. -/
def apmSubtractionMap (x : ℝ) : C(ℝ, ℝ) :=
  ⟨fun t => x - t, by fun_prop⟩

lemma apm_continuous_subtractionMap : Continuous apmSubtractionMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  simp only [apmSubtractionMap, ContinuousMap.coe_mk]
  fun_prop

lemma apm_translation_symmDiff_tendsto_zero (B : Set ℝ) (hB : MeasurableSet B)
    (hBfin : volume B ≠ ⊤) (x : ℝ) :
    Tendsto (fun y => volume (((apmSubtractionMap y) ⁻¹' B) ∆
      ((apmSubtractionMap x) ⁻¹' B))) (nhds x) (nhds 0) := by
  apply tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume)
  · exact apm_continuous_subtractionMap.continuousAt
  · exact Eventually.of_forall fun y => volume.measurePreserving_sub_left y
  · exact volume.measurePreserving_sub_left x
  · exact hB.nullMeasurableSet
  · exact hBfin

def apmOverlapSet (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (x : ℝ) : MeasuredSets (volume : Measure ℝ) :=
  ⟨A ∩ (apmSubtractionMap x) ⁻¹' B,
    hA.inter ((volume.measurePreserving_sub_left x).measurable hB)⟩

lemma apm_continuous_overlapSet (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤) :
    Continuous (apmOverlapSet A B hA hB) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (apm_translation_symmDiff_tendsto_zero B hB hBfin x)
    (fun _ => bot_le) (fun y => ?_)
  rw [MeasuredSets.edist_def]
  change volume ((A ∩ (apmSubtractionMap y) ⁻¹' B) ∆
    (A ∩ (apmSubtractionMap x) ⁻¹' B)) ≤ _
  rw [← inter_symmDiff_distrib_left]
  exact measure_mono inter_subset_right

lemma apm_continuous_overlapMeasure (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBfin : volume B ≠ ⊤) :
    Continuous (fun x => volume (A ∩ (apmSubtractionMap x) ⁻¹' B)) := by
  exact MeasuredSets.continuous_measure.comp
    (apm_continuous_overlapSet A B hA hB hBfin)

lemma apm_convolution_eq_overlapReal (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (x : ℝ) :
    ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      (indicator B (1 : ℝ → ℝ))) x =
      volume.real (A ∩ (apmSubtractionMap x) ⁻¹' B) := by
  change _ = volume.real (A ∩ (fun t => x - t) ⁻¹' B)
  rw [← integral_indicator_one
    (hA.inter ((volume.measurePreserving_sub_left x).measurable hB))]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    by_cases htA : t ∈ A <;> by_cases htB : x - t ∈ B <;> simp [htA, htB]

lemma apm_continuous_convolution_indicator (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : volume A ≠ ⊤) (hBfin : volume B ≠ ⊤) :
    Continuous
      ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (indicator B (1 : ℝ → ℝ))) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [show ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (indicator B (1 : ℝ → ℝ))) =
      (fun y => volume.real (A ∩ (apmSubtractionMap y) ⁻¹' B)) from
    funext (apm_convolution_eq_overlapReal A B hA hB)]
  refine (ENNReal.continuousAt_toReal ?_).comp
    (apm_continuous_overlapMeasure A B hA hB hBfin).continuousAt
  exact ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)

theorem apm_a99j02
    {E : Set ℝ}
    (hE_measurable : MeasurableSet E)
    (hE_interval : E ⊆ Icc (0 : ℝ) 1)
    (hE_positive : 0 < volume E) :
    Continuous (apmIndicatorConvolution E) ∧
      ∃ ε : ℝ, 0 < ε ∧
        ∀ t : ℝ, |t| < ε → 0 < volume (E ∩ apmTranslate E t) := by
  have hEfin : volume E ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp [Real.volume_Icc])
      (measure_mono hE_interval)
  constructor
  · have hconv := apm_continuous_convolution_indicator E E
      hE_measurable hE_measurable hEfin hEfin
    rw [show apmIndicatorConvolution E =
        ((indicator E (1 : ℝ → ℝ))
          ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (indicator E (1 : ℝ → ℝ))) by
      funext x
      simp only [apmIndicatorConvolution, apmIndicator, convolution]
      apply integral_congr_ae
      exact Eventually.of_forall fun y => mul_comm _ _]
    exact hconv
  · let B : Set ℝ := (fun x : ℝ => -x) ⁻¹' E
    have hB : MeasurableSet B := hE_measurable.preimage measurable_neg
    have hBfin : volume B ≠ ⊤ := by
      rw [show volume B = volume E by
        exact (Measure.measurePreserving_neg (volume : Measure ℝ)).measure_preimage
          hE_measurable.nullMeasurableSet]
      exact hEfin
    let F : ℝ → ℝ≥0∞ := fun t => volume (E ∩ (apmSubtractionMap t) ⁻¹' B)
    have hFcont : Continuous F :=
      apm_continuous_overlapMeasure E B hE_measurable hB hBfin
    have hFzero : F 0 = volume E := by
      simp [F, B, apmSubtractionMap]
    have hopen : IsOpen {t | 0 < F t} := isOpen_lt continuous_const hFcont
    have hzero : (0 : ℝ) ∈ {t | 0 < F t} := by
      simpa [hFzero] using hE_positive
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen 0 hzero
    refine ⟨ε, hε, fun t ht => ?_⟩
    have htF : 0 < F t := hball (by simpa [Real.dist_eq] using ht)
    have htranslate :
        E ∩ (apmSubtractionMap t) ⁻¹' B = E ∩ apmTranslate E t := by
      ext y
      simp only [mem_inter_iff, mem_preimage, apmSubtractionMap,
        ContinuousMap.coe_mk, B, apmTranslate, mem_image]
      constructor
      · rintro ⟨hyE, hy⟩
        refine ⟨hyE, y - t, ?_, by ring⟩
        simpa only [neg_sub] using hy
      · rintro ⟨hyE, x, hxE, rfl⟩
        refine ⟨hyE, ?_⟩
        convert hxE using 1 <;> ring
    simpa [F, htranslate] using htF
