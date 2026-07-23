import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace

open MeasureTheory Filter Set Real

theorem a00J02
    (f f' : ℝ → ℝ)
    (hf0 : f 0 = 0)
    (hf'_int : IntervalIntegrable f' volume 0 1)
    (hf_ac : ∀ x ∈ Icc (0:ℝ) 1, f x = ∫ t in (0:ℝ)..x, f' t)
    (hf'_sq : IntegrableOn (fun x => (f' x) ^ 2) (Icc 0 1)) :
    Tendsto (fun x => f x / sqrt x) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  sorry

**Formalization notes:**
- Absolute continuity with f(0)=0 is encoded as `hf_ac`: f equals the interval integral of its derivative f' on [0,1]
- The L² condition ∫|f'|² < ∞ is encoded as `hf'_sq` via `IntegrableOn`
- The limit value is **0** (by Cauchy-Schwarz: |f(x)| ≤ √x · ‖f'‖_{L²([0,x])}, so f(x)/√x → 0)
- The one-sided limit x→0⁺ uses `nhdsWithin 0 (Ioi 0)`
