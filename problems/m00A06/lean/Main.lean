import Mathlib

/-!
# APM m00A06 — regularizing `1 / |x|` as a distribution

## Statement repairs

None.

## Encoding notes

Mathlib does not package the LF space `𝒟(ℝ)` as a dedicated type.  Test
functions are therefore kept as actual functions `ℝ → ℝ` together with the
predicates `ContDiff ℝ ∞` and `HasCompactSupport`.  Membership in `𝒟'` is
represented by a linear functional satisfying, on every compact support, the
standard order-one seminorm estimate in `φ` and `deriv φ`.
-/

open Set MeasureTheory

noncomputable def apm_m00a06_singularKernel (x : ℝ) : ℝ :=
  |x|⁻¹

def apm_m00a06_IsTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ

def apm_m00a06_IsDistribution
    (T : (ℝ → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ K : Set ℝ, IsCompact K →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : ℝ → ℝ, apm_m00a06_IsTestFunction φ → tsupport φ ⊆ K →
        |T φ| ≤ C *
          (sSup (range fun x : ℝ => |φ x|) +
            sSup (range fun x : ℝ => |deriv φ x|))

theorem apm_m00a06 :
    (∃ φ : ℝ → ℝ,
      apm_m00a06_IsTestFunction φ ∧
      ¬Integrable (fun x => apm_m00a06_singularKernel x * φ x)) ∧
    (∀ φ : ℝ → ℝ,
      apm_m00a06_IsTestFunction φ → φ 0 = 0 →
      Integrable (fun x => apm_m00a06_singularKernel x * φ x)) ∧
    (∃ T : (ℝ → ℝ) →ₗ[ℝ] ℝ,
      apm_m00a06_IsDistribution T ∧
      ∀ φ : ℝ → ℝ,
        apm_m00a06_IsTestFunction φ → φ 0 = 0 →
        T φ = ∫ x : ℝ, apm_m00a06_singularKernel x * φ x) := by
  sorry
