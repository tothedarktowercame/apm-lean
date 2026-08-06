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
  sorry
