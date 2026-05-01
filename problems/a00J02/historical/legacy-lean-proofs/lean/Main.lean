import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic

open MeasureTheory Filter

/-!
# x^{-1/2} f(x) → 0 for absolutely continuous f with f' ∈ L²

## Strategy

Since f is absolutely continuous with f(0) = 0:
  f(x) = ∫₀ˣ f'(t) dt

By Cauchy-Schwarz on L²([0,x]):
  |f(x)| = |∫₀ˣ f'(t) dt| ≤ ‖1‖_{L²([0,x])} · ‖f'‖_{L²([0,x])}
         = √x · (∫₀ˣ |f'(t)|² dt)^{1/2}

Dividing by √x:
  |x^{-1/2} f(x)| ≤ (∫₀ˣ |f'(t)|² dt)^{1/2} → 0 as x → 0⁺

The last step uses absolute continuity of the Lebesgue integral:
if g ∈ L¹, then ∫_E g → 0 as m(E) → 0. Applied to |f'|² ∈ L¹.
-/

theorem abs_cont_sqrt_limit
    (f : ℝ → ℝ) (f' : ℝ → ℝ)
    (hac : ∀ x ∈ Set.Icc 0 1, f x = ∫ t in (0)..x, f' t)
    (hf0 : f 0 = 0)
    (hf'_l2 : ∫ t in (0)..(1 : ℝ), ‖f' t‖ ^ 2 < ⊤) :
    Tendsto (fun x => x ^ (-(1:ℝ)/2) * f x) (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  sorry
