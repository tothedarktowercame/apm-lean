import Mathlib

/-!
# Scalar integration on the capped cylinder

This file evaluates the complete cylindrical contribution in frozen `t03J06`.
The two nonconstant angular terms cancel by reflection and half-turn symmetry;
Fubini then leaves the integral of the constant term over a rectangle.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

namespace ConstructionTargets.CappedCylinderSurfaceIntegral

def cylinderIntegrand (theta z : ℝ) : ℝ :=
  -(z ^ 2 * Real.exp (Real.cos theta * z) *
      Real.log (Real.cos theta ^ 2 + 1) - Real.sin theta) * Real.sin theta +
    (Real.cos theta + Real.sin theta ^ 2 * z ^ 3 *
      Real.cos (Real.sin theta ^ 2 + z ^ 2)) * Real.cos theta

def reflectedTerm (theta z : ℝ) : ℝ :=
  -(z ^ 2 * Real.exp (Real.cos theta * z) *
      Real.log (Real.cos theta ^ 2 + 1)) * Real.sin theta

def halfTurnTerm (theta z : ℝ) : ℝ :=
  Real.sin theta ^ 2 * z ^ 3 *
    Real.cos (Real.sin theta ^ 2 + z ^ 2) * Real.cos theta

theorem cylinderIntegrand_decomposition (theta z : ℝ) :
    cylinderIntegrand theta z =
      1 + reflectedTerm theta z + halfTurnTerm theta z := by
  rw [cylinderIntegrand, reflectedTerm, halfTurnTerm]
  rw [← Real.sin_sq_add_cos_sq theta]
  ring

private theorem continuous_reflectedTerm (z : ℝ) :
    Continuous (fun theta => reflectedTerm theta z) := by
  have hlog : Continuous (fun theta : ℝ =>
      Real.log (Real.cos theta ^ 2 + 1)) :=
    (Real.continuous_cos.pow 2 |>.add continuous_const).log
      (fun theta => (add_pos_of_nonneg_of_pos
        (sq_nonneg (Real.cos theta)) zero_lt_one).ne')
  have h := (((continuous_const : Continuous fun _ : ℝ => z ^ 2).mul
    ((Real.continuous_exp.comp
      (Real.continuous_cos.mul
        (continuous_const : Continuous fun _ : ℝ => z))).mul hlog)).neg).mul
          Real.continuous_sin
  apply h.congr
  intro theta
  rw [reflectedTerm]
  simp only [Pi.mul_apply, Function.comp_apply]
  ring

private theorem continuous_halfTurnTerm (z : ℝ) :
    Continuous (fun theta => halfTurnTerm theta z) := by
  unfold halfTurnTerm
  fun_prop

theorem reflectedTerm_two_pi_sub (theta z : ℝ) :
    reflectedTerm (2 * Real.pi - theta) z = -reflectedTerm theta z := by
  simp only [reflectedTerm, Real.cos_two_pi_sub, Real.sin_two_pi_sub]
  ring

theorem halfTurnTerm_add_pi (theta z : ℝ) :
    halfTurnTerm (theta + Real.pi) z = -halfTurnTerm theta z := by
  simp only [halfTurnTerm, Real.sin_add_pi, Real.cos_add_pi]
  ring

/-- A continuous function odd under reflection about the interval midpoint
has zero integral on that interval. -/
theorem integral_zero_two_pi_reflection (f : ℝ → ℝ)
    (hreflect : ∀ theta, f (2 * Real.pi - theta) = -f theta) :
    (∫ theta in (0 : ℝ)..2 * Real.pi, f theta) = 0 := by
  have hchange := intervalIntegral.integral_comp_sub_left
    (a := (0 : ℝ)) (b := 2 * Real.pi) f (2 * Real.pi)
  have hleft :
      (∫ theta in (0 : ℝ)..2 * Real.pi, f (2 * Real.pi - theta)) =
        -(∫ theta in (0 : ℝ)..2 * Real.pi, f theta) := by
    rw [intervalIntegral.integral_congr (fun theta _ => hreflect theta)]
    rw [intervalIntegral.integral_neg]
  rw [hleft] at hchange
  have hpi : 0 < Real.pi := Real.pi_pos
  norm_num at hchange
  linarith

/-- A continuous function changing sign under a half turn has zero integral
over a full turn. -/
theorem integral_zero_two_pi_halfTurn (f : ℝ → ℝ) (hf : Continuous f)
    (hturn : ∀ theta, f (theta + Real.pi) = -f theta) :
    (∫ theta in (0 : ℝ)..2 * Real.pi, f theta) = 0 := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 Real.pi) (hf.intervalIntegrable Real.pi (2 * Real.pi))]
  have hshift := intervalIntegral.integral_comp_add_right
    (a := (0 : ℝ)) (b := Real.pi) f Real.pi
  have hsecond :
      (∫ theta in Real.pi..2 * Real.pi, f theta) =
        -(∫ theta in (0 : ℝ)..Real.pi, f theta) := by
    have hshift' :
        (∫ theta in (0 : ℝ)..Real.pi, f (theta + Real.pi)) =
          ∫ theta in Real.pi..2 * Real.pi, f theta := by
      convert hshift using 1 <;> ring
    rw [← hshift', intervalIntegral.integral_congr (fun theta _ => hturn theta),
      intervalIntegral.integral_neg]
  rw [hsecond]
  ring

theorem integral_reflectedTerm (z : ℝ) :
    (∫ theta in (0 : ℝ)..2 * Real.pi, reflectedTerm theta z) = 0 :=
  integral_zero_two_pi_reflection _ (fun theta => reflectedTerm_two_pi_sub theta z)

theorem integral_halfTurnTerm (z : ℝ) :
    (∫ theta in (0 : ℝ)..2 * Real.pi, halfTurnTerm theta z) = 0 :=
  integral_zero_two_pi_halfTurn _ (continuous_halfTurnTerm z)
    (fun theta => halfTurnTerm_add_pi theta z)

/-- For every fixed height, the angular integral of the frozen cylindrical
pullback is exactly the length of the angular interval. -/
theorem angular_integral_cylinderIntegrand (z : ℝ) :
    (∫ theta in (0 : ℝ)..2 * Real.pi, cylinderIntegrand theta z) =
      2 * Real.pi := by
  rw [intervalIntegral.integral_congr
    (fun theta _ => cylinderIntegrand_decomposition theta z)]
  have h12 := intervalIntegral.integral_add
    (μ := volume)
    (f := fun _ : ℝ => (1 : ℝ))
    (g := fun theta => reflectedTerm theta z)
    (continuous_const.intervalIntegrable (0 : ℝ) (2 * Real.pi))
    ((continuous_reflectedTerm z).intervalIntegrable _ _)
  have h123 := intervalIntegral.integral_add
    (μ := volume)
    (f := fun theta => (1 : ℝ) + reflectedTerm theta z)
    (g := fun theta => halfTurnTerm theta z)
    ((continuous_const.add (continuous_reflectedTerm z)).intervalIntegrable
      (0 : ℝ) (2 * Real.pi))
    ((continuous_halfTurnTerm z).intervalIntegrable _ _)
  rw [h123, h12, integral_reflectedTerm, integral_halfTurnTerm]
  simp

private theorem continuous_cylinderIntegrand :
    Continuous (Function.uncurry cylinderIntegrand) := by
  have hlog : Continuous (fun p : ℝ × ℝ =>
      Real.log (Real.cos p.1 ^ 2 + 1)) :=
    ((Real.continuous_cos.comp continuous_fst).pow 2 |>.add continuous_const).log
      (fun p => (add_pos_of_nonneg_of_pos
        (sq_nonneg (Real.cos p.1)) zero_lt_one).ne')
  have href : Continuous (fun p : ℝ × ℝ => reflectedTerm p.1 p.2) := by
    have h := (((continuous_snd.pow 2).mul
      ((Real.continuous_exp.comp
        ((Real.continuous_cos.comp continuous_fst).mul continuous_snd)).mul hlog)).neg.mul
          (Real.continuous_sin.comp continuous_fst))
    apply h.congr
    intro p
    rw [reflectedTerm]
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  have hhalf : Continuous (fun p : ℝ × ℝ => halfTurnTerm p.1 p.2) := by
    unfold halfTurnTerm
    fun_prop
  have hsum : Continuous (fun p : ℝ × ℝ =>
      1 + reflectedTerm p.1 p.2 + halfTurnTerm p.1 p.2) :=
    (continuous_const.add href).add hhalf
  apply hsum.congr
  intro p
  exact (cylinderIntegrand_decomposition p.1 p.2).symm

private theorem integrable_cylinderIntegrand_rectangle :
    Integrable (Function.uncurry cylinderIntegrand)
      ((volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict (uIoc (-1 : ℝ) 1))) := by
  rw [Measure.prod_restrict]
  apply (ContinuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc) continuous_cylinderIntegrand.continuousOn).mono_set
  exact prod_mono uIoc_subset_uIcc uIoc_subset_uIcc

/-- The entire cylindrical part of the frozen surface integral is `4π`. -/
theorem cylinder_surface_integral :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
      ∫ z in (-1 : ℝ)..1, cylinderIntegrand theta z) = 4 * Real.pi := by
  have hswap := MeasureTheory.intervalIntegral_integral_swap
    (a := (0 : ℝ)) (b := 2 * Real.pi)
    (μ := volume.restrict (uIoc (-1 : ℝ) 1))
    integrable_cylinderIntegrand_rectangle
  have hz : (-1 : ℝ) ≤ 1 := by norm_num
  simp only [uIoc_of_le hz] at hswap
  simp_rw [intervalIntegral.integral_of_le hz]
  rw [hswap]
  simp_rw [angular_integral_cylinderIntegrand]
  simp
  ring

/-- Adapter for the frozen pullback computation: any parametrized two-form
whose cylindrical evaluation is the compiled scalar formula contributes
exactly `4π`. -/
theorem cylinder_surface_integral_of_pointwise
    (pullback : ℝ → ℝ → ℝ)
    (hpullback : ∀ theta z, pullback theta z = cylinderIntegrand theta z) :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
      ∫ z in (-1 : ℝ)..1, pullback theta z) = 4 * Real.pi := by
  simp_rw [hpullback]
  exact cylinder_surface_integral

#print axioms integral_zero_two_pi_reflection
#print axioms integral_zero_two_pi_halfTurn
#print axioms angular_integral_cylinderIntegrand
#print axioms cylinder_surface_integral
#print axioms cylinder_surface_integral_of_pointwise

end ConstructionTargets.CappedCylinderSurfaceIntegral
