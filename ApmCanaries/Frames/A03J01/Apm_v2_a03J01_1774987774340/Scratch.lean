import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory Set ENNReal

noncomputable section

-- The key decomposition: f(x) for ℕ-valued f
-- In my hdecomp, the issue is f x = j vs j = f x ordering
-- tsum_eq_single needs the lambda to return 0 when j ≠ f x
-- but my condition is "if f x = j" which is the right order for the indicator.

-- Test the EXACT pattern I need:
example (n : ℕ) :
    (n : ℝ≥0∞) = ∑' (j : ℕ), if n = j then (j : ℝ≥0∞) else 0 := by
  conv_lhs => rw [show (n : ℝ≥0∞) = if n = n then (n : ℝ≥0∞) else 0 from by simp]
  exact (tsum_eq_single n (by intro j hj; exact if_neg hj)).symm
