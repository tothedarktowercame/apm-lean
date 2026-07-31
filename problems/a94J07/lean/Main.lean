import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

/-!
# APM a94J07: e^z + 8z + z³ is injective on the unit disk

The proof uses direct Lipschitz estimates for the two nonlinear terms.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Metric Real Set

open scoped Real

namespace ApmCanaries.A94J07

noncomputable def f_poly_exp (z : ℂ) : ℂ := cexp z + 8 * z + z ^ 3

/-- Bound: |e^z| ≤ e on |z| ≤ 1. -/
lemma norm_exp_le_e {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖cexp z‖ ≤ Real.exp 1 := by
  rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
  linarith [abs_re_le_norm z, le_abs_self (z.re)]

/-- Rouché estimate: |e^z + 3z²| < 8 on |z| = 1.
    This is also the derivative perturbation estimate. -/
lemma rouche_deriv_bound {z : ℂ} (hz : ‖z‖ = 1) :
    ‖cexp z + 3 * z ^ 2‖ < 8 := by
  have hexp := norm_exp_le_e hz.le
  calc
    ‖cexp z + 3 * z ^ 2‖ ≤ ‖cexp z‖ + ‖3 * z ^ 2‖ := norm_add_le _ _
    _ ≤ Real.exp 1 + 3 := by
      gcongr
      norm_num [norm_mul, norm_pow, hz]
    _ < 8 := by linarith [Real.exp_one_lt_three]

/-- Rouché estimate: |e^z + z³| < |8z| on |z| = 1. -/
lemma rouche_f_bound {z : ℂ} (hz : ‖z‖ = 1) :
    ‖cexp z + z ^ 3‖ < ‖(8 : ℂ) * z‖ := by
  have hexp := norm_exp_le_e hz.le
  calc
    ‖cexp z + z ^ 3‖ ≤ ‖cexp z‖ + ‖z ^ 3‖ := norm_add_le _ _
    _ ≤ Real.exp 1 + 1 := by
      gcongr
      simp [norm_pow, hz]
    _ < ‖(8 : ℂ) * z‖ := by
      rw [norm_mul, hz]
      norm_num
      linarith [Real.exp_one_lt_three]

/-- The derivative is nonzero because its constant term dominates the
    remaining terms throughout the closed unit disk. -/
lemma f_poly_exp_deriv_ne_zero
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    deriv f_poly_exp z ≠ 0 := by
  have hderiv :
      HasDerivAt f_poly_exp (cexp z + 8 + 3 * z ^ 2) z := by
    unfold f_poly_exp
    convert
      ((Complex.hasDerivAt_exp z).add ((hasDerivAt_id z).const_mul 8)).add
        (hasDerivAt_pow 3 z) using 1
    all_goals ring
  rw [hderiv.deriv]
  intro hzero
  have hperturb : cexp z + 3 * z ^ 2 = -8 := by
    linear_combination hzero
  have hnorm : ‖cexp z + 3 * z ^ 2‖ = 8 := by
    rw [hperturb]
    norm_num
  have hz_norm : ‖z‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hz
  have hexp := norm_exp_le_e hz_norm
  have hlt : ‖cexp z + 3 * z ^ 2‖ < 8 := by
    calc
      ‖cexp z + 3 * z ^ 2‖ ≤ ‖cexp z‖ + ‖3 * z ^ 2‖ := norm_add_le _ _
      _ ≤ Real.exp 1 + 3 := by
        gcongr
        rw [norm_mul, norm_pow]
        norm_num
        nlinarith [norm_nonneg z]
      _ < 8 := by linarith [Real.exp_one_lt_three]
  linarith

/-- The exponential and cubic perturbations are together strictly less
    expansive than the linear term on the unit disk. -/
theorem f_poly_exp_injective_on_disk :
    Set.InjOn f_poly_exp (ball (0 : ℂ) 1) := by
  intro x hx y hy hxy
  have hx_norm : ‖x‖ ≤ 1 := by
    have hxlt : ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx
    exact hxlt.le
  have hy_norm : ‖y‖ ≤ 1 := by
    have hylt : ‖y‖ < 1 := by simpa [mem_ball, dist_zero_right] using hy
    exact hylt.le
  have hexp_sub :
      ‖cexp x - cexp y‖ ≤ Real.exp 1 * ‖x - y‖ := by
    simpa only [sub_eq_add_neg] using
      (Convex.norm_image_sub_le_of_norm_deriv_le
        (s := ball (0 : ℂ) 1) (x := y) (y := x)
        (fun z _ => (Complex.hasDerivAt_exp z).differentiableAt)
        (fun z hz => by
          rw [(Complex.hasDerivAt_exp z).deriv]
          apply norm_exp_le_e
          have hzlt : ‖z‖ < 1 := by simpa [mem_ball, dist_zero_right] using hz
          exact hzlt.le)
        (convex_ball 0 1) hy hx)
  have hfactor : ‖x ^ 2 + x * y + y ^ 2‖ ≤ 3 := by
    calc
      ‖x ^ 2 + x * y + y ^ 2‖
          ≤ ‖x ^ 2 + x * y‖ + ‖y ^ 2‖ := norm_add_le _ _
      _ ≤ (‖x ^ 2‖ + ‖x * y‖) + ‖y ^ 2‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (1 + 1) + 1 := by
        gcongr
        · rw [norm_pow]
          nlinarith [norm_nonneg x]
        · rw [norm_mul]
          nlinarith [norm_nonneg x, norm_nonneg y]
        · rw [norm_pow]
          nlinarith [norm_nonneg y]
      _ = 3 := by norm_num
  have hcube_sub : ‖x ^ 3 - y ^ 3‖ ≤ 3 * ‖x - y‖ := by
    have hcube :
        x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
    rw [hcube, norm_mul]
    nlinarith [norm_nonneg (x - y)]
  by_contra hne
  have hnorm_pos : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hlinear :
      8 * ‖x - y‖ ≤ ‖cexp x - cexp y‖ + ‖x ^ 3 - y ^ 3‖ := by
    have heq :
        (8 : ℂ) * (x - y) = -((cexp x - cexp y) + (x ^ 3 - y ^ 3)) := by
      unfold f_poly_exp at hxy
      linear_combination hxy
    calc
      8 * ‖x - y‖ = ‖(8 : ℂ) * (x - y)‖ := by norm_num [norm_mul]
      _ = ‖(cexp x - cexp y) + (x ^ 3 - y ^ 3)‖ := by rw [heq, norm_neg]
      _ ≤ ‖cexp x - cexp y‖ + ‖x ^ 3 - y ^ 3‖ := norm_add_le _ _
  have hperturb :
      ‖cexp x - cexp y‖ + ‖x ^ 3 - y ^ 3‖ < 8 * ‖x - y‖ := by
    calc
      ‖cexp x - cexp y‖ + ‖x ^ 3 - y ^ 3‖
          ≤ Real.exp 1 * ‖x - y‖ + 3 * ‖x - y‖ :=
        add_le_add hexp_sub hcube_sub
      _ = (Real.exp 1 + 3) * ‖x - y‖ := by ring
      _ < 8 * ‖x - y‖ :=
        mul_lt_mul_of_pos_right (by linarith [Real.exp_one_lt_three]) hnorm_pos
  exact (not_lt_of_ge hlinear) hperturb

end ApmCanaries.A94J07
