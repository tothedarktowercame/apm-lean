import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open MeasureTheory Filter

/-- For f absolutely continuous on [0,1] with f(0) = 0 and f' ∈ L²,
    the limit of x^{-1/2} f(x) as x → 0⁺ is 0. -/
theorem abs_cont_sqrt_limit
    (f : ℝ → ℝ) (f' : ℝ → ℝ)
    (hac : ∀ x ∈ Set.Icc 0 1, f x = ∫ t in (0)..x, f' t)
    (hf0 : f 0 = 0)
    (hf'_l2 : ∫ t in (0)..(1 : ℝ), ‖f' t‖ ^ 2 < ⊤) :
    Tendsto (fun x => x ^ (-(1:ℝ)/2) * f x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  sorry
