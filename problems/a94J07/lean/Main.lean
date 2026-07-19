import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# APM a94J07: e^z + 8z + z³ is injective on the unit disk

The proof requires Rouché's theorem (not in Mathlib). The key numerical
bounds `|e^z + 3z²| ≤ e + 3 < 8` and `|e^z + z³| ≤ e + 1 < |8z|` are
partially proved below.
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
    SORRY: the norm arithmetic chain needs careful plumbing. -/
lemma rouche_deriv_bound {z : ℂ} (hz : ‖z‖ = 1) :
    ‖cexp z + 3 * z ^ 2‖ < 8 := by
  have hexp := norm_exp_le_e hz.le
  sorry

/-- Rouché estimate: |e^z + z³| < |8z| on |z| = 1.
    SORRY: same norm arithmetic issue. -/
lemma rouche_f_bound {z : ℂ} (hz : ‖z‖ = 1) :
    ‖cexp z + z ^ 3‖ < ‖(8 : ℂ) * z‖ := by
  have hexp := norm_exp_le_e hz.le
  sorry

/-- f' has no zeros (requires Rouché's theorem). -/
lemma f_poly_exp_deriv_ne_zero
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    deriv f_poly_exp z ≠ 0 := by
  sorry

/-- Main theorem: f is injective on the unit disk (requires Rouché's theorem). -/
theorem f_poly_exp_injective_on_disk :
    Set.InjOn f_poly_exp (ball (0 : ℂ) 1) := by
  sorry

end ApmCanaries.A94J07
