import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set Filter

noncomputable section

def ballSliceRadius (t : ℝ) : ℝ :=
  if |t| ≤ 1 then Real.sqrt (1 - t ^ 2) else 0

lemma ballSliceRadius_nonneg (t : ℝ) : 0 ≤ ballSliceRadius t := by
  unfold ballSliceRadius
  split_ifs with h
  · exact Real.sqrt_nonneg _
  · exact le_refl 0

lemma ballSliceRadius_le_one (t : ℝ) : ballSliceRadius t ≤ 1 := by
  unfold ballSliceRadius
  split_ifs with h
  · have h1 : 1 - t ^ 2 ≤ 1 := by nlinarith [sq_nonneg t]
    calc Real.sqrt (1 - t ^ 2)
        ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
      _ = 1 := Real.sqrt_one
  · exact zero_le_one

lemma ballSliceRadius_lt_one {t : ℝ} (ht : |t| ≤ 1) (ht0 : t ≠ 0) :
    ballSliceRadius t < 1 := by
  unfold ballSliceRadius
  rw [if_pos ht]
  have htabs := abs_le.mp ht
  have htsq : 0 < t ^ 2 := by positivity
  have h1 : 0 ≤ 1 - t ^ 2 := by nlinarith [htabs.1, htabs.2]
  have h2 : 1 - t ^ 2 < 1 := by linarith
  calc Real.sqrt (1 - t ^ 2)
      < Real.sqrt 1 := Real.sqrt_lt_sqrt h1 h2
    _ = 1 := Real.sqrt_one

/-- Pointwise: f(t)^n → 0 for t ≠ 0. -/
lemma ballSliceRadius_pow_tendsto {t : ℝ} (ht0 : t ≠ 0) :
    Tendsto (fun n => (ballSliceRadius t) ^ n) atTop (nhds 0) := by
  by_cases h : |t| ≤ 1
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one
      (ballSliceRadius_nonneg t)
      (ballSliceRadius_lt_one h ht0)
  · have hbr : ballSliceRadius t = 0 := by simp [ballSliceRadius, if_neg h]
    simp [hbr]
