/-
! # APM a96J02: A+B contains an open interval when μ(A),μ(B) > 0

## Problem

Let A and B be Lebesgue measurable subsets of ℝ having positive Lebesgue
measure. Prove that A+B = {a+b | a∈A, b∈B} contains a nonempty open interval.

## Proof (Steinhaus's theorem)

Step 1: Reduce to finite measure. Since A = ⋃_n (A ∩ [-n,n]) and μ(A) > 0,
some A' := A ∩ [-n,n] has 0 < μ(A') < ∞. Similarly find B' ⊂ B.

Step 2: Define f(x) = μ(A' ∩ (x - B')).

Step 3: By Fubini, ∫ f(x) dx = μ(A')μ(B') > 0.

Step 4: f is continuous (L¹ translation continuity via DCT).

Step 5: Since ∫f > 0, f(x₀) > 0 for some x₀. By continuity, f > 0 on an
open neighborhood of x₀. f(x) > 0 ⟹ A' ∩ (x - B') ≠ ∅ ⟹ x ∈ A' + B' ⊂ A+B.

## Dependencies

- DCT for continuity of convolution
  (Memory: e-codexpilot-prove-Holder-convolution-vanishes-at-infinity-by-compact-support-density)
- Monotone approximation for bounded subset reduction
  (Memory: math-informal/monotone-approximation)
-/

import Mathlib

open Set MeasureTheory Filter Topology Pointwise ENNReal
open scoped Convolution symmDiff

noncomputable section

/-- If A has positive measure, then A ∩ Icc(-n,n) has positive measure for
some n. -/
lemma exists_pos_measure_bounded_subset (A : Set ℝ) (hA : MeasurableSet A)
    (hApos : 0 < volume A) :
    ∃ n : ℕ, 0 < volume (A ∩ Set.Icc (-(n : ℝ)) n) := by
  have hcover : A ⊆ ⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n := by
    intro x hx
    simp only [mem_iUnion]
    refine ⟨Nat.ceil (abs x + 1), ⟨hx, ?_, ?_⟩⟩
    · have : (abs x : ℝ) ≤ Nat.ceil (abs x + 1) := by
        apply le_trans (by linarith : abs x ≤ abs x + 1)
        exact Nat.le_ceil (abs x + 1)
      linarith [neg_abs_le x]
    · apply le_trans (le_abs_self x)
      exact le_trans (by linarith : abs x ≤ abs x + 1) (Nat.le_ceil (abs x + 1))
  have hpos_union : 0 < volume (⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n) :=
    hApos.trans_le (measure_mono hcover)
  by_contra h
  push_neg at h
  have hzero : ∀ n : ℕ, volume (A ∩ Set.Icc (-(n : ℝ)) n) = 0 := fun n =>
    le_antisymm (h n) bot_le
  have hle : volume (⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n) ≤
      ∑' n : ℕ, volume (A ∩ Set.Icc (-(n : ℝ)) n) :=
    measure_iUnion_le _
  rw [show ∑' n : ℕ, volume (A ∩ Set.Icc (-(n : ℝ)) n) = 0 from by simp [hzero]] at hle
  have : volume (⋃ n : ℕ, A ∩ Set.Icc (-(n : ℝ)) n) = 0 :=
    le_antisymm hle bot_le
  rw [this] at hpos_union
  exact absurd hpos_union (lt_irrefl 0)

/-- Integrability of indicator of a finite-measure measurable set. -/
lemma integrable_indicator_of_finite_measure (s : Set ℝ) (hs : MeasurableSet s)
    (hsfin : volume s < ⊤) :
    Integrable (indicator s (1 : ℝ → ℝ)) volume := by
  rw [integrable_indicator_iff hs]
  refine ⟨aestronglyMeasurable_const, ?_⟩
  unfold HasFiniteIntegral
  simp [hsfin]

/- The key API missed by the starter search is
`tendsto_measure_symmDiff_preimage_nhds_zero`: it packages translation
continuity in measure for arbitrary finite measurable sets.  This is exactly
the L¹-indicator bridge suggested by the related a99J02 informal proof, and
avoids any pointwise claim at the boundary of the set. -/
def subtractionMap (x : ℝ) : C(ℝ, ℝ) := ⟨fun t => x - t, by fun_prop⟩

lemma continuous_subtractionMap : Continuous subtractionMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  simp only [subtractionMap, ContinuousMap.coe_mk]
  fun_prop

lemma translation_symmDiff_tendsto_zero (B : Set ℝ) (hB : MeasurableSet B)
    (hBfin : volume B ≠ ∞) (x : ℝ) :
    Tendsto (fun y => volume (((subtractionMap y) ⁻¹' B) ∆
      ((subtractionMap x) ⁻¹' B))) (𝓝 x) (𝓝 0) := by
  apply tendsto_measure_symmDiff_preimage_nhds_zero (μ := volume) (ν := volume)
  · exact continuous_subtractionMap.continuousAt
  · exact Eventually.of_forall fun y => volume.measurePreserving_sub_left y
  · exact volume.measurePreserving_sub_left x
  · exact hB.nullMeasurableSet
  · exact hBfin

def overlapSet (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (x : ℝ) : MeasuredSets (volume : Measure ℝ) :=
  ⟨A ∩ (subtractionMap x) ⁻¹' B,
    hA.inter ((volume.measurePreserving_sub_left x).measurable hB)⟩

lemma continuous_overlapSet (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBfin : volume B ≠ ∞) :
    Continuous (overlapSet A B hA hB) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_edist_tendsto_0]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (translation_symmDiff_tendsto_zero B hB hBfin x) (fun _ => bot_le) (fun y => ?_)
  · rw [MeasuredSets.edist_def]
    change volume ((A ∩ (subtractionMap y) ⁻¹' B) ∆
      (A ∩ (subtractionMap x) ⁻¹' B)) ≤ _
    rw [← inter_symmDiff_distrib_left]
    exact measure_mono inter_subset_right

lemma continuous_overlapMeasure (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hBfin : volume B ≠ ∞) :
    Continuous (fun x => volume (A ∩ (subtractionMap x) ⁻¹' B)) := by
  exact MeasuredSets.continuous_measure.comp (continuous_overlapSet A B hA hB hBfin)

lemma convolution_indicator_eq_overlapReal (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (x : ℝ) :
    ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      (indicator B (1 : ℝ → ℝ))) x =
      volume.real (A ∩ (subtractionMap x) ⁻¹' B) := by
  change _ = volume.real (A ∩ (fun t => x - t) ⁻¹' B)
  rw [← integral_indicator_one
    (hA.inter ((volume.measurePreserving_sub_left x).measurable hB))]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    by_cases htA : t ∈ A <;> by_cases htB : x - t ∈ B <;> simp [htA, htB]

lemma continuous_convolution_indicator (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAfin : volume A ≠ ∞) (hBfin : volume B ≠ ∞) :
    Continuous
      ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (indicator B (1 : ℝ → ℝ))) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [show ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (indicator B (1 : ℝ → ℝ))) =
      (fun y => volume.real (A ∩ (subtractionMap y) ⁻¹' B)) from
    funext (convolution_indicator_eq_overlapReal A B hA hB)]
  refine (ENNReal.continuousAt_toReal ?_).comp
    (continuous_overlapMeasure A B hA hB hBfin).continuousAt
  exact ne_top_of_le_ne_top hAfin (measure_mono inter_subset_left)

lemma positive_convolution_exists (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAint : Integrable (indicator A (1 : ℝ → ℝ)) volume)
    (hBint : Integrable (indicator B (1 : ℝ → ℝ)) volume)
    (hApos : 0 < volume A) (hBpos : 0 < volume B)
    (hAfin : volume A ≠ ∞) (hBfin : volume B ≠ ∞) :
    ∃ x : ℝ, 0 <
      ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (indicator B (1 : ℝ → ℝ))) x := by
  let F := ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
    (indicator B (1 : ℝ → ℝ)))
  have hint : ∫ x, F x = volume.real A * volume.real B := by
    dsimp [F]
    rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hAint hBint,
      integral_indicator_one hA, integral_indicator_one hB]
    rfl
  have hpos : 0 < ∫ x, F x := by
    rw [hint]
    exact mul_pos (ENNReal.toReal_pos hApos.ne' hAfin)
      (ENNReal.toReal_pos hBpos.ne' hBfin)
  by_contra h
  push_neg at h
  exact (not_lt_of_ge (integral_nonpos h)) hpos

lemma measurable_sum_contains_interval (A B : Set ℝ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAint : Integrable (indicator A (1 : ℝ → ℝ)) volume)
    (hBint : Integrable (indicator B (1 : ℝ → ℝ)) volume)
    (hApos : 0 < volume A) (hBpos : 0 < volume B)
    (hAfin : volume A ≠ ∞) (hBfin : volume B ≠ ∞) :
    ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ A + B := by
  let F := ((indicator A (1 : ℝ → ℝ)) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
    (indicator B (1 : ℝ → ℝ)))
  have hFcont : Continuous F := continuous_convolution_indicator A B hA hB hAfin hBfin
  obtain ⟨x, hx⟩ := positive_convolution_exists A B hA hB hAint hBint
    hApos hBpos hAfin hBfin
  have hopen : IsOpen {y | 0 < F y} := isOpen_lt continuous_const hFcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen x hx
  refine ⟨x - ε / 2, x + ε / 2, by linarith, ?_⟩
  intro y hy
  have hyball : y ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hypos : 0 < F y := hball hyball
  have hoverpos : 0 < volume.real (A ∩ (subtractionMap y) ⁻¹' B) := by
    rw [← convolution_indicator_eq_overlapReal A B hA hB]
    exact hypos
  obtain ⟨t, htA, htB⟩ := nonempty_of_measureReal_ne_zero hoverpos.ne'
  exact ⟨t, htA, y - t, htB, by ring⟩

/-- **Steinhaus's theorem**: If A and B are measurable subsets of ℝ with
positive Lebesgue measure, then A+B contains a nonempty open interval.

The proof uses the overlap function f(x) = μ(A' ∩ (x - B')) which is
continuous (by L¹ translation continuity), has positive integral (by Fubini),
and hence is positive on an open neighborhood that lies in A+B.

The continuity bridge is supplied by
`tendsto_measure_symmDiff_preimage_nhds_zero`: translations of a finite
measurable set converge in symmetric-difference measure. Intersecting with A'
is nonexpansive for that distance, so the overlap measure, hence the indicator
convolution, is continuous. Fubini gives its positive integral. -/
theorem a96J02 (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hApos : 0 < volume A) (hBpos : 0 < volume B) :
    ∃ a b : ℝ, a < b ∧ Set.Ioo a b ⊆ (A + B : Set ℝ) := by
  -- Step 1: Reduce to bounded subsets with positive finite measure
  obtain ⟨nA, hnA⟩ := exists_pos_measure_bounded_subset A hA hApos
  obtain ⟨nB, hnB⟩ := exists_pos_measure_bounded_subset B hB hBpos
  let A' := A ∩ Set.Icc (-(nA : ℝ)) nA
  let B' := B ∩ Set.Icc (-(nB : ℝ)) nB
  have hA'meas : MeasurableSet A' := hA.inter measurableSet_Icc
  have hB'meas : MeasurableSet B' := hB.inter measurableSet_Icc
  have hA'pos : 0 < volume A' := hnA
  have hB'pos : 0 < volume B' := hnB
  have hA'finite : volume A' < ⊤ :=
    (measure_mono (fun _ hx => hx.2)).trans_lt (by
      rw [Real.volume_Icc]; exact ofReal_lt_top)
  have hB'finite : volume B' < ⊤ :=
    (measure_mono (fun _ hx => hx.2)).trans_lt (by
      rw [Real.volume_Icc]; exact ofReal_lt_top)
  have hAB : A' + B' ⊆ A + B := by
    rintro x ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, ha.1, b, hb.1, rfl⟩
  have hA'int : Integrable (indicator A' (1 : ℝ → ℝ)) volume :=
    integrable_indicator_of_finite_measure _ hA'meas hA'finite
  have hB'int : Integrable (indicator B' (1 : ℝ → ℝ)) volume :=
    integrable_indicator_of_finite_measure _ hB'meas hB'finite
  obtain ⟨a, b, hab, hsub⟩ := measurable_sum_contains_interval A' B' hA'meas hB'meas
    hA'int hB'int hA'pos hB'pos hA'finite.ne hB'finite.ne
  exact ⟨a, b, hab, hsub.trans hAB⟩

end
