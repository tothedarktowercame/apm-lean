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

private lemma apm_m00a06_continuous_dslope_zero
    {φ : ℝ → ℝ} (hφ : Differentiable ℝ φ) :
    Continuous (dslope φ 0) := by
  rw [← continuousOn_univ]
  exact (continuousOn_dslope Filter.univ_mem).2
    ⟨hφ.continuous.continuousOn, hφ.differentiableAt⟩

private lemma apm_m00a06_kernel_mul_eq_sign_mul_dslope
    {φ : ℝ → ℝ} (hφ0 : φ 0 = 0) {x : ℝ} (hx : x ≠ 0) :
    apm_m00a06_singularKernel x * φ x =
      (|x|⁻¹ * x) * dslope φ 0 x := by
  rw [dslope_of_ne _ hx, slope_def_field, hφ0]
  simp only [sub_zero]
  unfold apm_m00a06_singularKernel
  field_simp

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
        Boundary (closer hop 1) for integrability after cancellation: the new
        lemmas `apm_m00a06_continuous_dslope_zero` and
        `apm_m00a06_kernel_mul_eq_sign_mul_dslope` route around derivative
        supremum estimates.  The integrand is a.e. the continuous divided
        difference `dslope φ 0` multiplied by `|x|⁻¹*x`, whose norm is one
        off the null singleton `{0}`.  Since `φ 0 = 0`, the divided difference
        vanishes outside `support φ` (apart from zero), hence has compact
        support and is integrable by
        `Continuous.integrable_of_hasCompactSupport`. The remaining short API
        bridge is packaging that compact-support inclusion and applying
        `Integrable.bdd_mul` plus a.e. congruence.
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
