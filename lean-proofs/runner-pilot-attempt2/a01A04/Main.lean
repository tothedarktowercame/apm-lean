import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set Filter Topology

noncomputable section

def ballSlice (t : ℝ) : ℝ :=
  if |t| ≤ 1 then Real.sqrt (1 - t ^ 2) else 0

lemma ballSlice_nonneg (t : ℝ) : 0 ≤ ballSlice t := by
  unfold ballSlice; split_ifs <;> [exact Real.sqrt_nonneg _; exact le_refl 0]

lemma ballSlice_le_one (t : ℝ) : ballSlice t ≤ 1 := by
  unfold ballSlice; split_ifs with h
  · calc Real.sqrt (1 - t ^ 2) ≤ Real.sqrt 1 :=
        Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
      _ = 1 := Real.sqrt_one
  · exact zero_le_one

lemma ballSlice_lt_one {t : ℝ} (ht : |t| ≤ 1) (ht0 : t ≠ 0) :
    ballSlice t < 1 := by
  unfold ballSlice; rw [if_pos ht]
  have htabs := abs_le.mp ht
  have htsq : 0 < t ^ 2 := by positivity
  calc Real.sqrt (1 - t ^ 2) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt (by nlinarith [htabs.1, htabs.2]) (by linarith)
    _ = 1 := Real.sqrt_one

lemma ballSlice_pow_tendsto {t : ℝ} (ht0 : t ≠ 0) :
    Tendsto (fun n => (ballSlice t) ^ n) atTop (nhds 0) := by
  by_cases h : |t| ≤ 1
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (ballSlice_nonneg t) (ballSlice_lt_one h ht0)
  · have : ballSlice t = 0 := by simp [ballSlice, if_neg h]
    simp [this]

lemma ballSlice_eq_zero_of_abs_gt_one {t : ℝ} (h : 1 < |t|) :
    ballSlice t = 0 := by
  simp [ballSlice, if_neg (not_le.mpr h)]

lemma abs_ballSlice_le_one (t : ℝ) : |ballSlice t| ≤ 1 := by
  rw [abs_le]; exact ⟨by linarith [ballSlice_nonneg t], ballSlice_le_one t⟩

lemma abs_gt_one_of_not_mem_Icc {t : ℝ} (h : t ∉ Set.Icc (-1 : ℝ) 1) : 1 < |t| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; exact h

lemma norm_ballSlice_pow_le (n : ℕ) (hn : n ≠ 0) (t : ℝ) :
    ‖(ballSlice t) ^ n‖ ≤ (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t := by
  rw [Real.norm_eq_abs, abs_pow, Set.indicator_apply]
  split_ifs with h
  · exact pow_le_one₀ (abs_nonneg _) (abs_ballSlice_le_one t)
  · rw [ballSlice_eq_zero_of_abs_gt_one (abs_gt_one_of_not_mem_Icc h), abs_zero, zero_pow hn]

-- Indicator integrable: ∫ 𝟙_{[-1,1]} = 2 < ∞
lemma indicator_Icc_integrable :
    Integrable ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ))) volume := by
  rw [integrable_indicator_iff measurableSet_Icc]
  apply integrableOn_const <;> simp [Real.volume_Icc, ENNReal.ofReal_ne_top]
  -- autoparams should handle: volume (Icc (-1) 1) ≠ ⊤ and ‖1‖ₑ ≠ ⊤

-- Part (b): ∫ ballSlice^(n+1) → 0
-- 1 sorry remaining: DCT wiring.
-- HtDP design sketch:
--   Apply tendsto_integral_of_dominated_convergence with:
--     F n t := (ballSlice t) ^ (n+1)
--     f t   := 0
--     bound := indicator_{[-1,1]} 1
--   Need: (a) ∀ n, AEStronglyMeasurable (F n) volume
--         (b) ∀ᶠ n, ∀ᵐ t, ‖F n t‖ ≤ bound t  [norm_ballSlice_pow_le]
--         (c) ∀ᵐ t, Tendsto (F · t) atTop (nhds 0)  [ballSlice_pow_tendsto]
--         (d) Integrable bound  [indicator_Icc_integrable]
--   Blocked on (a): AEStronglyMeasurable for ballSlice^n.
--   ballSlice is piecewise continuous (sqrt on closed set, 0 elsewhere)
--   → Measurable → StronglyMeasurable → AEStronglyMeasurable.
--   The Measurable proof needs: measurable_sqrt, Measurable.pow,
--   Measurable.piecewise on measurableSet_Icc.
theorem ballSlice_integral_tendsto_zero :
    Tendsto (fun n => ∫ t, (ballSlice t) ^ (n + 1)) atTop (nhds 0) := by
  sorry
