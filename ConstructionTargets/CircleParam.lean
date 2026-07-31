import Mathlib

/-!
# Unit-interval parametrization of a circle integral

This module bridges the exponential parametrization on `[0,1]` with
Mathlib's standard `circleIntegral` parametrization on `[0, 2π]`.
-/

open Complex MeasureTheory Real Set

noncomputable section

namespace ConstructionTargets.CircleParam

/-- The `[0,1]` exponential parametrization of a circle agrees with Mathlib's
standard circle integral after the linear substitution `θ = 2πt`. -/
theorem unitParam_eq_circleIntegral (R : ℝ) (g : ℂ → ℂ)
    (hg : ContinuousOn g (Metric.sphere 0 |R|)) :
    (∫ t in (0 : ℝ)..1,
        g (R * Complex.exp (2 * π * I * t)) *
          deriv (fun u : ℝ ↦ R * Complex.exp (2 * π * I * u)) t) =
      ∮ z in C(0, R), g z := by
  let phi : ℝ → ℝ := fun t ↦ 2 * π * t
  let h : ℝ → ℂ := fun theta ↦
    deriv (circleMap 0 R) theta * g (circleMap 0 R theta)
  have hphi : ∀ t : ℝ, HasDerivAt phi (2 * π) t := by
    intro t
    simpa [phi] using (hasDerivAt_id t).const_mul (2 * π)
  have hphi' : ContinuousOn (fun _ : ℝ ↦ 2 * π) (uIcc (0 : ℝ) 1) :=
    continuous_const.continuousOn
  have hgcomp : Continuous (fun theta : ℝ ↦ g (circleMap 0 R theta)) :=
    hg.comp_continuous (continuous_circleMap 0 R) fun theta ↦
      circleMap_mem_sphere' 0 R theta
  have hh : Continuous h := by
    simp only [h, deriv_circleMap]
    exact ((continuous_circleMap 0 R).mul continuous_const).mul hgcomp
  have hsub := intervalIntegral.integral_deriv_smul_comp'
    (a := (0 : ℝ)) (b := 1) (f := phi) (f' := fun _ ↦ 2 * π) (g := h)
    (fun t _ ↦ hphi t) hphi' hh.continuousOn
  calc
    (∫ t in (0 : ℝ)..1,
        g (R * Complex.exp (2 * π * I * t)) *
          deriv (fun u : ℝ ↦ R * Complex.exp (2 * π * I * u)) t) =
        ∫ t in (0 : ℝ)..1, (2 * π : ℝ) • (h ∘ phi) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hfun :
          (fun u : ℝ ↦ R * Complex.exp (2 * π * I * u)) =
            circleMap 0 R ∘ phi := by
        funext u
        simp only [phi, circleMap, Function.comp_apply, zero_add]
        congr 2
        push_cast
        ring
      have hderiv :
          deriv (fun u : ℝ ↦ R * Complex.exp (2 * π * I * u)) t =
            (2 * π : ℝ) • (circleMap 0 R (2 * π * t) * I) := by
        rw [hfun]
        convert (((hasDerivAt_circleMap 0 R (phi t)).scomp t (hphi t)).deriv) using 1
      change
        g (R * Complex.exp (2 * π * I * t)) *
            deriv (fun u : ℝ ↦ R * Complex.exp (2 * π * I * u)) t =
          (2 * π : ℝ) • (h ∘ phi) t
      rw [hderiv]
      simp only [h, phi, Function.comp_apply, deriv_circleMap, circleMap, zero_add,
        real_smul, Complex.ofReal_mul]
      norm_num
      ring
    _ = ∫ theta in phi 0..phi 1, h theta := hsub
    _ = ∮ z in C(0, R), g z := by
      simp [phi, h, circleIntegral, smul_eq_mul]

end ConstructionTargets.CircleParam
