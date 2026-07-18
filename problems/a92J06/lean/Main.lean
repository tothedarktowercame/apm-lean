import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# APM a92J06: Trigonometric integral via contour integration

**Problem.** Evaluate ∫₀²π 1/(2 + cos θ) dθ via contour integration.
**Answer: 2π/√3.**
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Real
open scoped Topology

namespace ApmCanaries.A92J06

/-- √3 > 1. -/
lemma sqrt_three_gt_one : 1 < sqrt 3 := by
  have h : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h

/-- (sqrt 3 : ℂ) ^ 2 = 3. -/
lemma sq_sqrt_three_complex : (sqrt 3 : ℂ) ^ 2 = 3 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)

/-- z² + 4z + 1 = (z - z₁)(z - z₂) where z₁ = -2+√3, z₂ = -2-√3. -/
lemma quadratic_factor (z : ℂ) :
    z ^ 2 + 4 * z + 1 = (z - ((-2 : ℂ) + (sqrt 3 : ℂ))) *
                        (z - ((-2 : ℂ) - (sqrt 3 : ℂ))) := by
  have h3 : (sqrt 3 : ℂ) ^ 2 = 3 := sq_sqrt_three_complex
  linear_combination h3

/-- |z₁| < 1: z₁ = -2+√3 has |z₁| = 2-√3 < 1. -/
lemma z1_norm_lt_one : ‖((-2 : ℂ) + (sqrt 3 : ℂ))‖ < 1 := by
  rw [show ‖((-2 : ℂ) + (sqrt 3 : ℂ))‖ = ‖(↑(sqrt 3 - 2) : ℂ)‖ by
    congr 1; simp; ring]
  rw [Complex.norm_real]
  rw [show ‖(sqrt 3 - 2 : ℝ)‖ = 2 - sqrt 3 by
    rw [Real.norm_eq_abs, abs_of_nonpos]
    · linarith
    · nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num),
                 Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), sqrt_three_gt_one]]
  linarith [sqrt_three_gt_one]

/-- |z₂| > 1: z₂ = -2-√3 has |z₂| = 2+√3 > 1. -/
lemma z2_norm_gt_one : 1 < ‖((-2 : ℂ) - (sqrt 3 : ℂ))‖ := by
  rw [show ‖((-2 : ℂ) - (sqrt 3 : ℂ))‖ = ‖(↑(-(sqrt 3 + 2)) : ℂ)‖ by
    congr 1; simp; ring]
  rw [Complex.norm_real]
  rw [show ‖(-((sqrt 3 + 2) : ℝ))‖ = sqrt 3 + 2 by
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg]
    linarith [sqrt_three_gt_one]]
  linarith [sqrt_three_gt_one]

/-- The contour integral ∮_{|z|=1} 2/(i(z²+4z+1)) dz = 2π/√3.

    **SORRY BOUNDARY:** Requires partial fraction decomposition and
    application of `integral_sub_inv_of_mem_ball` for the root inside the
    disk and `integral_sub_zpow_of_ne` for the root outside. -/
lemma contour_integral_eval :
    (∮ z in C((0 : ℂ), 1), (2 : ℂ) / (I * (z ^ 2 + 4 * z + 1))) =
      Complex.ofReal (2 * π / sqrt 3) := by
  sorry

/-- Main theorem: ∫₀²π 1/(2 + cos θ) dθ = 2π/√3.

    **SORRY BOUNDARY:** The z = e^{iθ} substitution requires change of
    variables for complex-valued interval integrals on the circle. -/
theorem integral_inv_two_plus_cos :
    ∫ θ in (0 : ℝ)..2 * π, 1 / (2 + Real.cos θ) = 2 * π / sqrt 3 := by
  sorry

end ApmCanaries.A92J06
