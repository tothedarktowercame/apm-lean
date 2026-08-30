import Mathlib

/-! # The nonzero period obstruction for `x dy - y dx` on the unit circle -/

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.CirclePeriodObstruction

abbrev E3 := EuclideanSpace ℝ (Fin 3)
abbrev Circle3 := {x : E3 // x 0 ^ 2 + x 1 ^ 2 = 1 ∧ x 2 = 0}
abbrev CircleForm1 := Circle3 → E3 →L[ℝ] ℝ

def IsAlpha (alpha : E3 → E3 [⋀^Fin 1]→L[ℝ] ℝ) : Prop :=
  ∀ x v, alpha x v = x 0 * v 0 1 - x 1 * v 0 0

def IsRestriction (alpha : E3 → E3 [⋀^Fin 1]→L[ℝ] ℝ)
    (alpha' : CircleForm1) : Prop :=
  ∀ x v, alpha' x v = alpha x (fun _ ↦ v)

def IsDifferential (f : Circle3 → ℝ) (alpha' : CircleForm1) : Prop :=
  ∀ c : ℝ → Circle3,
    Differentiable ℝ (fun t => (c t : E3)) →
    Differentiable ℝ (fun t => f (c t)) ∧
      ∀ t, deriv (fun s => f (c s)) t =
        alpha' (c t) (deriv (fun s => (c s : E3)) t)

def circleAmbient (t : ℝ) : E3 :=
  Real.cos t • EuclideanSpace.single 0 (1 : ℝ) +
    Real.sin t • EuclideanSpace.single 1 (1 : ℝ)

def circleParam (t : ℝ) : Circle3 := ⟨circleAmbient t, by
  constructor
  · simp [circleAmbient]
  · simp [circleAmbient]⟩

def circleTangent (t : ℝ) : E3 :=
  (-Real.sin t) • EuclideanSpace.single 0 (1 : ℝ) +
    Real.cos t • EuclideanSpace.single 1 (1 : ℝ)

theorem hasDerivAt_circleAmbient (t : ℝ) :
    HasDerivAt circleAmbient (circleTangent t) t := by
  exact ((Real.hasDerivAt_cos t).smul_const
      (EuclideanSpace.single 0 (1 : ℝ))).add
    ((Real.hasDerivAt_sin t).smul_const
      (EuclideanSpace.single 1 (1 : ℝ)))

theorem circleAmbient_periodic : circleAmbient (2 * Real.pi) = circleAmbient 0 := by
  simp [circleAmbient]

theorem alpha_circle_tangent
    (alpha : E3 → E3 [⋀^Fin 1]→L[ℝ] ℝ) (ha : IsAlpha alpha) (t : ℝ) :
    alpha (circleAmbient t) (fun _ ↦ circleTangent t) = 1 := by
  rw [ha]
  simp [circleAmbient, circleTangent]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem restricted_circle_period
    (alpha : E3 → E3 [⋀^Fin 1]→L[ℝ] ℝ) (ha : IsAlpha alpha)
    (alpha' : CircleForm1) (ha' : IsRestriction alpha alpha') :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      alpha' (circleParam t) (deriv circleAmbient t)) = 2 * Real.pi := by
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
        alpha' (circleParam t) (deriv circleAmbient t)) =
        ∫ _t in (0 : ℝ)..2 * Real.pi, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t _
      change alpha' (circleParam t) (deriv circleAmbient t) = 1
      rw [(hasDerivAt_circleAmbient t).deriv, ha']
      exact alpha_circle_tangent alpha ha t
    _ = 2 * Real.pi := by simp

theorem circle_not_differential
    (alpha : E3 → E3 [⋀^Fin 1]→L[ℝ] ℝ) (ha : IsAlpha alpha)
    (alpha' : CircleForm1) (ha' : IsRestriction alpha alpha') :
    ¬ ∃ f : Circle3 → ℝ, IsDifferential f alpha' := by
  rintro ⟨f, hf⟩
  obtain ⟨hfdiff, hfderiv⟩ := hf circleParam
    (fun t ↦ (hasDerivAt_circleAmbient t).differentiableAt)
  have hcambient : (fun s : ℝ ↦ ((circleParam s : Circle3) : E3)) = circleAmbient := rfl
  have hderiv_one : ∀ t : ℝ, deriv (fun s ↦ f (circleParam s)) t = 1 := by
    intro t
    rw [hfderiv t, hcambient, (hasDerivAt_circleAmbient t).deriv, ha']
    exact alpha_circle_tangent alpha ha t
  have hinterv : IntervalIntegrable (deriv (fun s ↦ f (circleParam s)))
      volume 0 (2 * Real.pi) := by
    apply (continuous_const.intervalIntegrable 0 (2 * Real.pi)).congr
    intro t _
    exact (hderiv_one t).symm
  have hFTC :
      (∫ t in (0 : ℝ)..2 * Real.pi, deriv (fun s ↦ f (circleParam s)) t) = 0 := by
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun t _ ↦ hfdiff.differentiableAt)
      hinterv]
    have hc : circleParam (2 * Real.pi) = circleParam 0 := by
      apply Subtype.ext
      exact circleAmbient_periodic
    rw [hc, sub_self]
  rw [intervalIntegral.integral_congr (fun t _ ↦ hderiv_one t)] at hFTC
  simp at hFTC

#print axioms hasDerivAt_circleAmbient
#print axioms alpha_circle_tangent
#print axioms restricted_circle_period
#print axioms circle_not_differential

end ConstructionTargets.CirclePeriodObstruction
