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
      have hdsupp : HasCompactSupport (dslope φ 0) := by
        apply HasCompactSupport.intro (hφ.2.isCompact.union isCompact_singleton)
        intro x hx
        have hx0 : x ≠ 0 := by
          intro h
          subst x
          exact hx (Or.inr rfl)
        have hxt : x ∉ tsupport φ := fun h => hx (Or.inl h)
        have hxs : x ∉ Function.support φ := fun h => hxt (subset_tsupport φ h)
        have hφx : φ x = 0 := not_ne_iff.mp hxs
        rw [dslope_of_ne _ hx0, slope_def_field, hφ0]
        simp [hφx]
      have hdsint : Integrable (dslope φ 0) :=
        (apm_m00a06_continuous_dslope_zero hφdiff).integrable_of_hasCompactSupport hdsupp
      have hsign_meas : AEStronglyMeasurable (fun x : ℝ => |x|⁻¹ * x) := by
        fun_prop
      have hsign_bound : ∀ᵐ x : ℝ, ‖|x|⁻¹ * x‖ ≤ (1 : ℝ) := by
        filter_upwards [] with x
        by_cases hx : x = 0
        · simp [hx]
        · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_abs, inv_mul_cancel₀ (abs_ne_zero.mpr hx)]
      have hprod : Integrable (fun x : ℝ => (|x|⁻¹ * x) * dslope φ 0 x) :=
        hdsint.bdd_mul hsign_meas hsign_bound
      apply hprod.congr
      filter_upwards [volume.ae_ne (0 : ℝ)] with x hx
      exact (apm_m00a06_kernel_mul_eq_sign_mul_dslope hφ0 hx).symm
    · /-
      Boundary for the finite-part distribution: define the linear map by the
      two integrals over `Icc (-1) 1` and its complement, subtracting `φ 0`
      in the first. Besides the cancellation lemma isolated in the preceding
      conjunct, the frozen custom predicate requires a uniform order-one
      estimate for every compact `K`. This needs enclosing `K` in `[-R,R]`,
      converting the mean-value estimate into the two global `sSup (range …)`
      terms, and proving the split integral agrees with the original integral
      when `φ 0 = 0`. No sibling solved artifact contains this construction.
      Closer hop 2 closes the preceding cancellation-integrability conjunct by
      proving compact support of `dslope φ 0`, bounding the sign multiplier,
      and applying a.e. congruence off `{0}`. The remaining construction can
      reuse that result, but its uniform estimate and linear-map assembly are
      still open.
      -/
      sorry
