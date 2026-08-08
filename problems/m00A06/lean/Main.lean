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

/-- Why this unblocks `apm_m00a06`: this is the missing finite-part
functional, expressed by its two regularized integrals.  The distribution
clause is exactly the compact-support order-one seminorm estimate required by
the frozen encoding. -/
theorem apm_m00A06_bridge_finitePart :
    ∃ T : (ℝ → ℝ) →ₗ[ℝ] ℝ,
      apm_m00a06_IsDistribution T ∧
      ∀ φ : ℝ → ℝ, apm_m00a06_IsTestFunction φ →
        T φ =
          (∫ x in Icc (-1 : ℝ) 1,
            apm_m00a06_singularKernel x * (φ x - φ 0)) +
          ∫ x in (Icc (-1 : ℝ) 1)ᶜ,
            apm_m00a06_singularKernel x * φ x := by
  sorry

/-- Why this unblocks `apm_m00a06`: when the test function vanishes at the
origin, the regularization disappears and the two set integrals recombine into
the ordinary singular integral demanded by the main theorem. -/
theorem apm_m00A06_bridge_finitePart_eq_integral
    {φ : ℝ → ℝ} (hφ : apm_m00a06_IsTestFunction φ) (hφ0 : φ 0 = 0) :
    (∫ x in Icc (-1 : ℝ) 1,
        apm_m00a06_singularKernel x * (φ x - φ 0)) +
      ∫ x in (Icc (-1 : ℝ) 1)ᶜ,
        apm_m00a06_singularKernel x * φ x =
      ∫ x : ℝ, apm_m00a06_singularKernel x * φ x := by
  sorry

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
  · let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    refine ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩, ?_⟩
    intro hint
    have hi : IntervalIntegrable
        (fun x => apm_m00a06_singularKernel x * b x) volume 0 1 :=
      hint.intervalIntegrable
    have heq : Set.EqOn
        (fun x => apm_m00a06_singularKernel x * b x)
        (fun x : ℝ => x⁻¹) (uIoc 0 1) := by
      intro x hx
      have hxi : x ∈ Icc (0 : ℝ) 1 := by
        rw [uIoc_of_le (by norm_num)] at hx
        exact ⟨hx.1.le, hx.2⟩
      have hb : b x = 1 := b.one_of_mem_closedBall (by
        change dist x 0 ≤ 1
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hxi.1]
        exact hxi.2)
      simp [apm_m00a06_singularKernel, hb, abs_of_nonneg hxi.1]
    have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 :=
      hi.congr heq
    rw [intervalIntegrable_inv_iff] at hinv
    simp at hinv
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
      Closer hop 3 closes the divergent-witness conjunct using a
      `ContDiffBump` equal to one on `[0,1]` and Mathlib's exact
      `intervalIntegrable_inv_iff`. The finite-part distribution remains open:
      it requires bundling the two regularized integrals as a linear map and
      proving the frozen compact-support seminorm estimate uniformly in `K`.
      -/
      sorry
