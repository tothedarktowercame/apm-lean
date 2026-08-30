import Mathlib

/-!
# Explicit cross-derivative calculus for the punctured-plane angle form

This file proves the first local bridge in frozen `t97J08`.  It computes the
two relevant Fréchet derivatives from the quotient formula and proves their
cross evaluations agree away from the origin.
-/

open scoped ContDiff

noncomputable section

namespace ConstructionTargets.ExplicitCrossDerivativeCalculus

abbrev OneForm := ℂ → ℂ → ℝ

def beta : OneForm := fun z v =>
  (z.re * v.im - z.im * v.re) /
    (2 * Real.pi * (z.re ^ 2 + z.im ^ 2))

def sqRadius (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

def denominator (z : ℂ) : ℝ := 2 * Real.pi * sqRadius z

theorem sqRadius_ne_zero {z : ℂ} (hz : z ≠ 0) : sqRadius z ≠ 0 := by
  intro h
  apply hz
  apply Complex.normSq_eq_zero.mp
  simpa [sqRadius, Complex.normSq_apply, pow_two] using h

theorem denominator_ne_zero {z : ℂ} (hz : z ≠ 0) : denominator z ≠ 0 :=
  mul_ne_zero (by positivity) (sqRadius_ne_zero hz)

@[simp] theorem beta_I (z : ℂ) : beta z Complex.I = z.re / denominator z := by
  simp [beta, denominator, sqRadius]

@[simp] theorem beta_one (z : ℂ) : beta z 1 = -z.im / denominator z := by
  simp [beta, denominator, sqRadius]

private theorem hasFDerivAt_sqRadius (z : ℂ) :
    HasFDerivAt sqRadius
      ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) z := by
  unfold sqRadius
  convert (Complex.reCLM.hasFDerivAt.pow 2).add
    (Complex.imCLM.hasFDerivAt.pow 2) using 1
  ext v
  simp

private theorem hasFDerivAt_denominator (z : ℂ) :
    HasFDerivAt denominator
      ((2 * Real.pi) •
        ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM)) z := by
  unfold denominator
  have h := (hasFDerivAt_const (x := z) (2 * Real.pi)).mul
    (hasFDerivAt_sqRadius z)
  convert h using 1
  ext v
  simp [sqRadius]

private theorem hasFDerivAt_inv_denominator (z : ℂ) (hz : z ≠ 0) :
    HasFDerivAt (fun w => (denominator w)⁻¹)
      ((-((denominator z)⁻¹ * (denominator z)⁻¹)) •
        ((2 * Real.pi) •
          ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM))) z := by
  have hi := (hasFDerivAt_inv' (denominator_ne_zero hz)).comp z
    (hasFDerivAt_denominator z)
  convert hi using 1
  ext v
  simp [ContinuousLinearMap.mulLeftRight_apply]
  ring

private theorem hasFDerivAt_beta_I (z : ℂ) (hz : z ≠ 0) :
    HasFDerivAt (fun w => beta w Complex.I)
      (Complex.reCLM.smulRight ((denominator z)⁻¹) +
        z.re • ((-((denominator z)⁻¹ * (denominator z)⁻¹)) •
          ((2 * Real.pi) •
            ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM)))) z := by
  rw [show (fun w => beta w Complex.I) =
      fun w => w.re * (denominator w)⁻¹ by funext w; simp [div_eq_mul_inv]]
  have h := Complex.reCLM.hasFDerivAt.mul (hasFDerivAt_inv_denominator z hz)
  convert h using 1
  ext v
  simp
  ring

private theorem hasFDerivAt_beta_one (z : ℂ) (hz : z ≠ 0) :
    HasFDerivAt (fun w => beta w 1)
      ((-Complex.imCLM).smulRight ((denominator z)⁻¹) +
        (-z.im) • ((-((denominator z)⁻¹ * (denominator z)⁻¹)) •
          ((2 * Real.pi) •
            ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM)))) z := by
  rw [show (fun w => beta w 1) =
      fun w => (-w.im) * (denominator w)⁻¹ by funext w; simp [div_eq_mul_inv]]
  have h := (-Complex.imCLM).hasFDerivAt.mul (hasFDerivAt_inv_denominator z hz)
  convert h using 1
  ext v
  simp
  ring

theorem beta_differentiableAt_coordinates (z : ℂ) (hz : z ≠ 0) :
    DifferentiableAt ℝ (fun w => beta w 1) z ∧
      DifferentiableAt ℝ (fun w => beta w Complex.I) z :=
  ⟨(hasFDerivAt_beta_one z hz).differentiableAt,
    (hasFDerivAt_beta_I z hz).differentiableAt⟩

/-- Exact parameterized form of frozen
`apm_t97J08_bridge_beta_cross_derivatives`. -/
theorem beta_cross_derivatives (z : ℂ) (hz : z ≠ 0) :
    (fderiv ℝ (fun w : ℂ => beta w Complex.I) z) 1 =
      (fderiv ℝ (fun w : ℂ => beta w 1) z) Complex.I := by
  rw [(hasFDerivAt_beta_I z hz).fderiv, (hasFDerivAt_beta_one z hz).fderiv]
  simp
  field_simp [denominator_ne_zero hz]
  simp [denominator, sqRadius]
  ring

def IsClosedOnPuncturedPlane (eta : OneForm) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    DifferentiableAt ℝ (fun w : ℂ => eta w 1) z ∧
    DifferentiableAt ℝ (fun w : ℂ => eta w Complex.I) z ∧
    (fderiv ℝ (fun w : ℂ => eta w Complex.I) z) 1 =
      (fderiv ℝ (fun w : ℂ => eta w 1) z) Complex.I

theorem beta_closed_on_puncturedPlane : IsClosedOnPuncturedPlane beta := by
  intro z hz
  exact ⟨(beta_differentiableAt_coordinates z hz).1,
    (beta_differentiableAt_coordinates z hz).2,
    beta_cross_derivatives z hz⟩

#print axioms beta_cross_derivatives
#print axioms beta_closed_on_puncturedPlane

end ConstructionTargets.ExplicitCrossDerivativeCalculus
