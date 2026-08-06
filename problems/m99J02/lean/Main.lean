import Mathlib

/-!
# APM m99J02

## Statement repairs

Part (b) is given the standard minimal regularity hypothesis that `q` is continuous.
The source calls `u₁,u₂` classical solutions of `u'' + q u = 0` but states no
regularity for `q`; continuity makes the regular distribution `q g_y` unambiguous.

## Encoding questions

Distributional identities are stated in their exact weak form against every smooth,
compactly supported test function. No scalar or pointwise surrogate replaces `𝒟'(ℝ)`.
-/

noncomputable section

def apm_m99j02_IsTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

def apm_m99j02_g (u₁ u₂ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  if x ≤ y then u₁ x * u₂ y else u₂ x * u₁ y

def apm_m99j02_Wronskian (u₁ u₂ : ℝ → ℝ) (y : ℝ) : ℝ :=
  u₁ y * deriv u₂ y - deriv u₁ y * u₂ y

def apm_m99j02_regularSecondDerivative
    (u₁ u₂ : ℝ → ℝ) (y x : ℝ) : ℝ :=
  if x < y then deriv (deriv u₁) x * u₂ y
  else deriv (deriv u₂) x * u₁ y

theorem apm_m99j02
    (u₁ u₂ : ℝ → ℝ) (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂) :
    (∀ (y : ℝ) (φ : ℝ → ℝ), apm_m99j02_IsTestFunction φ →
      (∫ x : ℝ, apm_m99j02_g u₁ u₂ y x * deriv (deriv φ) x) =
        (∫ x : ℝ, apm_m99j02_regularSecondDerivative u₁ u₂ y x * φ x) +
          apm_m99j02_Wronskian u₁ u₂ y * φ y) ∧
    ∀ q : ℝ → ℝ, Continuous q →
      (∀ x : ℝ, deriv (deriv u₁) x + q x * u₁ x = 0) →
      (∀ x : ℝ, deriv (deriv u₂) x + q x * u₂ x = 0) →
      ∀ (y : ℝ) (φ : ℝ → ℝ), apm_m99j02_IsTestFunction φ →
        (∫ x : ℝ, apm_m99j02_g u₁ u₂ y x *
          (deriv (deriv φ) x + q x * φ x)) =
            apm_m99j02_Wronskian u₁ u₂ 0 * φ y := by
  sorry
