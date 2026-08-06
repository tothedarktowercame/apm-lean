import Mathlib

/-!
# APM a97J04: Local absolute continuity at a boundary point

## Statement repairs

None.

## Encoding questions

None. A function on `[0,1]` is represented by an ambient `f : ℝ → ℝ` whose
hypotheses and conclusion are all restricted to the stated intervals. Bounded
variation and absolute continuity use Mathlib's `BoundedVariationOn` and
`AbsolutelyContinuousOnInterval` predicates directly.
-/

open Set

theorem apm_a97j04
    (f : ℝ → ℝ)
    (hcontinuous : ContinuousOn f (Icc (0 : ℝ) 1))
    (hvariation : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hlocal : ∀ δ : ℝ, 0 < δ → δ < 1 →
      AbsolutelyContinuousOnInterval f δ 1) :
    AbsolutelyContinuousOnInterval f 0 1 := by
  sorry
