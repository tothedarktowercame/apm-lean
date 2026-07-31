import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# APM a92J07: Entire function avoiding the nonpositive reals is constant

**Problem.** Let u,v : ℝ² → ℝ be C¹ with u_x = v_y, u_y = -v_x (Cauchy-Riemann).
If v(x,y) = 0 implies u(x,y) > 0, then u,v are constant.

## Proof

f = u + iv is entire (from CR). The hypothesis means f(ℂ) ⊆ slitPlane.
Then g = log ∘ f is entire with |Im g| ≤ π. So h = e^{ig} is bounded entire,
constant by Liouville → g constant → f constant.

## Statement repair note

We prove the complex formulation (entire + avoids (-∞,0] → constant).
The CR-to-complex reduction is a separate formalization challenge.
-/

set_option linter.unusedVariables false in
noncomputable section

open Complex Set
open scoped Topology Real

namespace ApmCanaries.A92J07

/-- **Main theorem:** An entire function whose image lies in `slitPlane`
    (avoids (-∞,0]) is constant. -/
theorem entire_avoids_ray_const
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (homit : ∀ z, f z ∈ slitPlane) :
    ∃ c : ℂ, ∀ z, f z = c := by
  -- g = log ∘ f is entire
  have hg : Differentiable ℂ (fun z => log (f z)) := hf.clog homit
  -- Im(g(z)) ∈ (-π, π], so |Im g| ≤ π
  have hg_im_bdd : ∀ z, ‖(log (f z)).im‖ ≤ π := fun z => by
    have h1 : (log (f z)).im = arg (f z) := log_im (f z)
    rw [h1, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [neg_pi_lt_arg (f z)], arg_le_pi (f z)⟩
  -- h = exp(I * log f) is bounded entire
  set h := fun z => exp (I * log (f z))
  have hh : Differentiable ℂ h := by fun_prop
  have hh_bdd : Bornology.IsBounded (range h) := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
    refine ⟨Real.exp π, ?_⟩
    rintro _ ⟨z, rfl⟩
    change dist (exp (I * log (f z))) (0 : ℂ) ≤ Real.exp π
    rw [dist_eq_norm, sub_zero, norm_exp]
    rw [show (I * log (f z)).re = -((log (f z)).im) from by
          rw [mul_comm]; exact mul_I_re (log (f z))]
    apply Real.exp_le_exp.mpr
    have hbd := hg_im_bdd z
    rw [Real.norm_eq_abs, abs_le] at hbd
    linarith
  -- By Liouville, h is constant
  obtain ⟨c, hc⟩ := hh.exists_const_forall_eq_of_bounded hh_bdd
  -- Differentiate the constant identity. Since `exp` and `I` are nonzero,
  -- the derivative of `log ∘ f` vanishes, so it is constant.
  have hh_deriv : ∀ z, deriv h z = 0 := fun z => by
    rw [show h = fun _ => c from funext hc]
    exact congrFun (deriv_const' c) z
  have hg_deriv : ∀ z, deriv (fun z => log (f z)) z = 0 := fun z => by
    have hinner :
        HasDerivAt (fun z => I * log (f z))
          (I * deriv (fun z => log (f z)) z) z :=
      (hg z).hasDerivAt.const_mul I
    have hhexp :
        HasDerivAt h
          (exp (I * log (f z)) * (I * deriv (fun z => log (f z)) z)) z := by
      simpa [h] using (hasDerivAt_exp (I * log (f z))).comp z hinner
    have hz :
        exp (I * log (f z)) * (I * deriv (fun z => log (f z)) z) = 0 := by
      rw [← hhexp.deriv, hh_deriv z]
    rcases mul_eq_zero.mp hz with hexp | hrest
    · exact (exp_ne_zero _ hexp).elim
    · exact (mul_eq_zero.mp hrest).resolve_left I_ne_zero
  have hg_const : ∀ z, log (f z) = log (f 0) :=
    fun z => is_const_of_deriv_eq_zero hg hg_deriv z 0
  refine ⟨f 0, fun z => ?_⟩
  rw [← exp_log (slitPlane_ne_zero (homit z)),
    ← exp_log (slitPlane_ne_zero (homit 0)), hg_const z]

/-- **Problem statement (CR form).**

    The component maps are continuously real differentiable, as required by the
    prose problem. Thus the displayed `deriv` values are genuine partial
    derivatives rather than junk values from totalization. -/
-- STATEMENT REPAIR 2026-07-31 (Joe-authorised): require C¹ component maps so
-- totalized `deriv` cannot make the Cauchy-Riemann premises vacuous.
theorem cauchy_riemann_ray_implies_const
    {u v : ℝ → ℝ → ℝ}
    (hC1 : ContDiff ℝ 1 (Function.uncurry u) ∧
      ContDiff ℝ 1 (Function.uncurry v))
    (hcr1 : ∀ x y, deriv (fun x' => u x' y) x = deriv (fun y' => v x y') y)
    (hcr2 : ∀ x y, deriv (fun y' => u x y') y = -(deriv (fun x' => v x' y) x))
    (hray : ∀ x y, v x y = 0 → 0 < u x y) :
    ∃ c₁ c₂ : ℝ, ∀ x y, u x y = c₁ ∧ v x y = c₂ := by
  sorry

end ApmCanaries.A92J07
