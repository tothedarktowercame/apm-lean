import Mathlib

/-!
# APM a98J02

## Statement repairs

* The printed numerator `|f(x)-f(y)|2` is repaired to
  `|f(x)-f(y)|²`, as required by the supplied argument and dimensional
  consistency.
* The existential `δ` is required to be positive; otherwise the conclusion
  would be vacuous.

## Encoding questions

The assertion `∫₀¹ |f'|² < ∞` is encoded as integrability of the squared
within-derivative on `[0,1]`. This avoids Lean's convention that the Bochner
integral of a nonintegrable function is defined to be zero.
-/

open MeasureTheory

theorem apm_a98j02 (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hderiv : IntegrableOn
      (fun x : ℝ => |derivWithin f (Set.Icc 0 1) x| ^ 2)
      (Set.Icc 0 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ, 0 ≤ y → y < x → x ≤ 1 → |x - y| < δ →
        |f x - f y| ^ 2 / |x - y| < ε := by
  sorry
