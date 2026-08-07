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

lemma apm_m99j02_wronskian_eq_zero
    (u₁ u₂ q : ℝ → ℝ) (hu₁ : ContDiff ℝ 2 u₁) (hu₂ : ContDiff ℝ 2 u₂)
    (hq₁ : ∀ x : ℝ, deriv (deriv u₁) x + q x * u₁ x = 0)
    (hq₂ : ∀ x : ℝ, deriv (deriv u₂) x + q x * u₂ x = 0) :
    ∀ y : ℝ, apm_m99j02_Wronskian u₁ u₂ y =
      apm_m99j02_Wronskian u₁ u₂ 0 := by
  have hu₁d : Differentiable ℝ u₁ := hu₁.differentiable (by norm_num)
  have hu₂d : Differentiable ℝ u₂ := hu₂.differentiable (by norm_num)
  have hdu₁d : Differentiable ℝ (deriv u₁) := hu₁.differentiable_deriv_two
  have hdu₂d : Differentiable ℝ (deriv u₂) := hu₂.differentiable_deriv_two
  have hW (x : ℝ) : HasDerivAt (apm_m99j02_Wronskian u₁ u₂) 0 x := by
    have hprod₁ := (hu₁d x).hasDerivAt.mul (hdu₂d x).hasDerivAt
    have hprod₂ := (hdu₁d x).hasDerivAt.mul (hu₂d x).hasDerivAt
    convert hprod₁.sub hprod₂ using 1
    rw [show deriv (deriv u₁) x = -(q x * u₁ x) from
        eq_neg_of_add_eq_zero_left (hq₁ x),
        show deriv (deriv u₂) x = -(q x * u₂ x) from
        eq_neg_of_add_eq_zero_left (hq₂ x)]
    ring
  intro y
  exact is_const_of_deriv_eq_zero
    (fun x => (hW x).differentiableAt) (fun x => (hW x).deriv) y 0

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
  have hregular_cancel :
      ∀ (q : ℝ → ℝ),
        (∀ x : ℝ, deriv (deriv u₁) x + q x * u₁ x = 0) →
        (∀ x : ℝ, deriv (deriv u₂) x + q x * u₂ x = 0) →
        ∀ (y x : ℝ), x ≠ y →
          apm_m99j02_regularSecondDerivative u₁ u₂ y x +
              q x * apm_m99j02_g u₁ u₂ y x = 0 := by
    intro q hq₁ hq₂ y x hxy
    by_cases hlt : x < y
    · rw [apm_m99j02_regularSecondDerivative, if_pos hlt,
        apm_m99j02_g, if_pos hlt.le]
      rw [show deriv (deriv u₁) x = -(q x * u₁ x) from
        eq_neg_of_add_eq_zero_left (hq₁ x)]
      ring
    · have hyx : y < x := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hxy)
      rw [apm_m99j02_regularSecondDerivative, if_neg hlt,
        apm_m99j02_g, if_neg (not_le.mpr hyx)]
      rw [show deriv (deriv u₂) x = -(q x * u₂ x) from
        eq_neg_of_add_eq_zero_left (hq₂ x)]
      ring
  /-
  Boundary: the regular part of the Green-function equation is proved above
  to vanish away from the gluing point. Completing the frozen statement still
  requires two integrations by parts on the half-lines. Abel's identity for
  the raw-`deriv` Wronskian is proved above. I searched the whole-line
  `MeasureTheory.integral_mul_deriv_eq_deriv_mul`, interval integration-by-parts,
  compact-support, and piecewise differentiability APIs, but did not find a
  route that packages the boundary limits and the derivative jump at `y`.
  -/
  sorry
