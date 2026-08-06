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
  constructor
  · /-
    Boundary for the divergent witness: the intended witness is a smooth bump
    equal to one near zero. Mathlib's `ContDiffBump` API supplies such
    functions, while non-integrability reduces to that of `|x|⁻¹` on a
    punctured neighborhood. Searches found `integrableOn_Ioc_iff_integral_norm_lt_top`
    and the power-integrability API, but no compiled bridge from the bump's
    plateau equations to `¬Integrable` for the product on all of `ℝ`.
    -/
    sorry
  · constructor
    · intro φ hφ hφ0
      have hφdiff : Differentiable ℝ φ := hφ.1.differentiable (by simp)
      have hφcont : Continuous φ := hφdiff.continuous
      have hsupport : HasCompactSupport
          (fun x => apm_m00a06_singularKernel x * φ x) := by
        exact hφ.2.mul_left
      have hat_zero : apm_m00a06_singularKernel 0 * φ 0 = 0 := by
        simp [apm_m00a06_singularKernel]
      /-
        Boundary for integrability after cancellation: `hφdiff` and `hφ0`
        let `Convex.norm_image_sub_le_of_norm_deriv_le` bound
        `|φ x| / |x|` by a derivative supremum. The product has compact
        support by `hsupport` and its value at the singular point is compiled
        as `hat_zero`. What remains is an API-level measurable domination
        proof: obtain a finite derivative bound on the compact convex hull of
        the support, prove the quotient is a.e. strongly measurable off the
        null singleton `{0}`, and dominate it by a constant times the indicator
        of a compact interval. `Continuous.integrable_of_hasCompactSupport`
        does not apply directly because division by `|x|` can have unequal
        one-sided limits at zero.
        -/
      sorry
    · /-
      Boundary for the finite-part distribution: define the linear map by the
      two integrals over `Icc (-1) 1` and its complement, subtracting `φ 0`
      in the first. Besides the cancellation lemma isolated in the preceding
      conjunct, the frozen custom predicate requires a uniform order-one
      estimate for every compact `K`. This needs enclosing `K` in `[-R,R]`,
      converting the mean-value estimate into the two global `sSup (range …)`
      terms, and proving the split integral agrees with the original integral
      when `φ 0 = 0`. No sibling solved artifact contains this construction.
      -/
      sorry
