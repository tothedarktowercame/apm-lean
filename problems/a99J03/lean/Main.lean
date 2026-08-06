import Mathlib

/-!
# APM a99J03: A Stieltjes transform of an `L¹` function

## Statement repairs

None.

## Encoding questions

None. The source's `L¹((0,∞))` is interpreted for real-valued functions
using Lebesgue measure. The final question at `a = 0` is encoded by the
explicit counterexample `1_(0,1)`.
-/

open MeasureTheory Set Filter
open scoped ContDiff

noncomputable section

/-- The Stieltjes-type transform in the problem. -/
def apm_a99J03_transform (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), f y / (x + y)

/-- The counterexample `f = 1_(0,1)` for the endpoint question. -/
def apm_a99J03_counterexample (y : ℝ) : ℝ :=
  (Ioo (0 : ℝ) 1).indicator (fun _ ↦ 1) y

theorem apm_a99j03
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
    ContDiffOn ℝ ∞ (apm_a99J03_transform f) (Ioi 0) ∧
    (∀ a : ℝ, 0 < a →
      IntegrableOn (deriv (apm_a99J03_transform f)) (Ici a)) ∧
    IntegrableOn apm_a99J03_counterexample (Ioi 0) ∧
    ¬IntegrableOn
      (deriv (apm_a99J03_transform apm_a99J03_counterexample))
      (Ioi 0) := by
  sorry
