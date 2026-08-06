import Mathlib

/-! # APM m99A06: a small convolution-quadratic equation in `L¹`

## Statement repairs

None.

## Encoding note

An `L¹` function is determined only almost everywhere, so the functional
equation is stated almost everywhere with respect to Lebesgue measure.  This is
the canonical faithful reading of an equation whose unknown is required only to
belong to `L¹(ℝ)`.
-/

open Filter MeasureTheory

noncomputable section

def m99A06SelfConvolution (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, f (x - y) * f y

def IsM99A06Solution (ε : ℝ) (f : ℝ → ℝ) : Prop :=
  Integrable f ∧
  ∀ᵐ x : ℝ ∂volume,
    f x + Real.sin x * m99A06SelfConvolution f x =
      ε * Real.exp (-|x| ^ 2)

theorem apm_m99a06 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ,
      0 < ε → ε < ε₀ → ∃ f : ℝ → ℝ, IsM99A06Solution ε f := by
  have hforcing : Integrable (fun x : ℝ ↦ Real.exp (-|x| ^ 2)) := by
    simpa [sq_abs] using
      (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))
  /-
  Boundary: integrability of the Gaussian forcing, needed to define the
  fixed-point self-map on `L¹`, is proved above. Completing the theorem requires
  working in the complete `L¹` quotient space, transporting the raw convolution
  to representatives, proving Young's inequality and the quadratic Lipschitz
  estimate, and applying Banach's fixed-point theorem on a closed ball before
  selecting a representative satisfying the equation almost everywhere. I
  searched Mathlib's `L1`, convolution/Young, bounded multiplier, closed-ball,
  and contraction APIs; I did not complete the quotient/representative bridge
  to the frozen raw-function predicate `IsM99A06Solution` in this pass.
  -/
  sorry
