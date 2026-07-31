import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Conformal
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
  let f : ℂ → ℂ := fun z =>
    Complex.equivRealProdCLM.symm
      (Function.uncurry u (z.re, z.im), Function.uncurry v (z.re, z.im))
  have hu : Differentiable ℝ (Function.uncurry u) := hC1.1.differentiable_one
  have hv : Differentiable ℝ (Function.uncurry v) := hC1.2.differentiable_one
  have hf_real : Differentiable ℝ f := by
    apply Complex.equivRealProdCLM.symm.differentiable.comp
    exact
      (hu.comp Complex.equivRealProdCLM.differentiable).prodMk
        (hv.comp Complex.equivRealProdCLM.differentiable)
  have hu_x (x y : ℝ) :
      deriv (fun x' => u x' y) x =
        fderiv ℝ (Function.uncurry u) (x, y) (1, 0) := by
    have h : HasFDerivAt (fun x' => u x' y)
        ((fderiv ℝ (Function.uncurry u) (x, y)).comp
          (ContinuousLinearMap.inl ℝ ℝ ℝ)) x := by
      simpa [Function.uncurry] using
        (hu (x, y)).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    simpa [Function.uncurry] using h.hasDerivAt.deriv
  have hu_y (x y : ℝ) :
      deriv (fun y' => u x y') y =
        fderiv ℝ (Function.uncurry u) (x, y) (0, 1) := by
    have h : HasFDerivAt (fun y' => u x y')
        ((fderiv ℝ (Function.uncurry u) (x, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ ℝ)) y := by
      simpa [Function.uncurry] using
        (hu (x, y)).hasFDerivAt.comp y
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
    simpa [Function.uncurry] using h.hasDerivAt.deriv
  have hv_x (x y : ℝ) :
      deriv (fun x' => v x' y) x =
        fderiv ℝ (Function.uncurry v) (x, y) (1, 0) := by
    have h : HasFDerivAt (fun x' => v x' y)
        ((fderiv ℝ (Function.uncurry v) (x, y)).comp
          (ContinuousLinearMap.inl ℝ ℝ ℝ)) x := by
      simpa [Function.uncurry] using
        (hv (x, y)).hasFDerivAt.comp x
          (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    simpa [Function.uncurry] using h.hasDerivAt.deriv
  have hv_y (x y : ℝ) :
      deriv (fun y' => v x y') y =
        fderiv ℝ (Function.uncurry v) (x, y) (0, 1) := by
    have h : HasFDerivAt (fun y' => v x y')
        ((fderiv ℝ (Function.uncurry v) (x, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ ℝ)) y := by
      simpa [Function.uncurry] using
        (hv (x, y)).hasFDerivAt.comp y
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y)
    simpa [Function.uncurry] using h.hasDerivAt.deriv
  have hf : Differentiable ℂ f := fun z => by
    rw [differentiableAt_complex_iff_differentiableAt_real]
    refine ⟨hf_real z, ?_⟩
    have hfu := hu (z.re, z.im)
    have hfv := hv (z.re, z.im)
    let D : ℂ →L[ℝ] ℂ :=
      Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp
        (((fderiv ℝ (Function.uncurry u) (z.re, z.im)).prod
          (fderiv ℝ (Function.uncurry v) (z.re, z.im))).comp
            Complex.equivRealProdCLM.toContinuousLinearMap)
    have hcomp :
        fderiv ℝ f z = D := by
      have hpair' :
          HasFDerivAt
            (fun z : ℂ =>
              (Function.uncurry u (z.re, z.im), Function.uncurry v (z.re, z.im)))
            (((fderiv ℝ (Function.uncurry u) (z.re, z.im)).prod
              (fderiv ℝ (Function.uncurry v) (z.re, z.im))).comp
                Complex.equivRealProdCLM.toContinuousLinearMap) z := by
        simpa using
          (hfu.hasFDerivAt.prodMk hfv.hasFDerivAt).comp z
            Complex.equivRealProdCLM.hasFDerivAt
      have hout :
          HasFDerivAt f D z := by
        simpa [f, D] using
          Complex.equivRealProdCLM.symm.hasFDerivAt.comp z hpair'
      exact hout.fderiv
    rw [hcomp]
    dsimp [D]
    apply Complex.ext <;>
      simp only [Complex.equivRealProdCLM_symm_apply, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, mul_zero, Complex.I_im, mul_one,
        sub_zero, Complex.add_im, zero_add, Complex.mul_im, Complex.I_re,
        Complex.I_mul]
    · rw [← hu_y, ← hv_x, hcr2]
      ring
    · rw [← hv_y, ← hu_x, hcr1]
  have homit : ∀ z, f z ∈ slitPlane := fun z => by
    rw [mem_slitPlane_iff]
    simp only [f, Complex.equivRealProdCLM_symm_apply, Function.uncurry_apply_pair,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
      Complex.I_im, sub_zero, Complex.add_im, zero_add, Complex.mul_im,
      Complex.I_re]
    by_cases hv0 : v z.re z.im = 0
    · left
      simpa using hray z.re z.im hv0
    · right
      simpa using hv0
  obtain ⟨c, hc⟩ := entire_avoids_ray_const hf homit
  refine ⟨c.re, c.im, fun x y => ?_⟩
  have hxy := hc (x + y * I)
  constructor
  · simpa [f, Complex.equivRealProdCLM_symm_apply] using congrArg Complex.re hxy
  · simpa [f, Complex.equivRealProdCLM_symm_apply] using congrArg Complex.im hxy

end ApmCanaries.A92J07
