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

lemma apm_a98J02_sub_eq_integral_deriv (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hx : x ≤ 1) :
    f x - f y = ∫ t in y..x, deriv f t := by
  symm
  apply AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
  apply hf.mono
  rw [Set.uIcc_of_le hyx, Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  exact Set.Icc_subset_Icc hy hx

theorem apm_a98j02 (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f 0 1)
    (hderiv : IntegrableOn
      (fun x : ℝ => |derivWithin f (Set.Icc 0 1) x| ^ 2)
      (Set.Icc 0 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x y : ℝ, 0 ≤ y → y < x → x ≤ 1 → |x - y| < δ →
        |f x - f y| ^ 2 / |x - y| < ε := by
  /- CLOSER HOP 1 BOUNDARY.

  `apm_a98J02_sub_eq_integral_deriv` now compiles the fundamental-theorem
  bridge on every subinterval `[y,x]`, by restricting the supplied absolute
  continuity hypothesis with `AbsolutelyContinuousOnInterval.mono` and using
  `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`.

  The remaining estimate is the analytic core.  One must identify `deriv f`
  with `derivWithin f (Icc 0 1)` almost everywhere on each interior
  subinterval, apply integral Cauchy--Schwarz to obtain
  `|f x-f y|² ≤ (x-y) * ∫_[y,x] |derivWithin f (Icc 0 1)|²`, and use
  absolute continuity of the integral of the integrable squared derivative to
  choose a uniform `δ`.  Mathlib supplies
  `Integrable.tendsto_setIntegral_nhds_zero` and the ENNReal/NNReal Hölder
  inequalities, but repository and source searches found no assembled
  real-valued interval lemma matching this `derivWithin` encoding.  No solved
  sibling or `ConstructionTargets` module closes those conversions.  The
  frozen statement is unchanged.
  -/
  sorry
