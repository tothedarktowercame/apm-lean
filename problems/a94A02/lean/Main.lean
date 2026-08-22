import Mathlib
import a01J03.lean.Main

open MeasureTheory Set

noncomputable section

/-!
# APM a94A02

## Statement repairs

None. The referenced `informal-solution.md` is absent from this problem bundle, so
the TeX statement alone was used as the contract.

## Encoding notes

The source's one-based sequence is reindexed by `ℕ`. The derivative sum `g` takes
values in `ENNReal`, honestly retaining the possible value `+∞`; its integrability
is therefore stated as finiteness of its `lintegral`. The equality with `f'` uses
`ENNReal.ofReal`, justified mathematically by monotonicity.
-/

noncomputable def apmFunctionSeries (f : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, f n x

noncomputable def apmDerivativeSeries (f : ℕ → ℝ → ℝ) (x : ℝ) : ENNReal := by
  classical
  exact if ∀ n, DifferentiableAt ℝ (f n) x then
    ∑' n, ENNReal.ofReal (deriv (f n) x)
  else 0

/-- The countable differentiability guard in `apmDerivativeSeries` holds almost
everywhere on the interval.  Thus the guard itself does not lose any mass. -/
lemma apm_a94a02_ae_all_differentiable
    (f : ℕ → ℝ → ℝ)
    (hf_ac : ∀ n, AbsolutelyContinuousOnInterval (f n) 0 1) :
    ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∀ n, DifferentiableAt ℝ (f n) x := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have h_all : ∀ᵐ x ∂volume, ∀ n,
      x ∈ uIcc (0 : ℝ) 1 → DifferentiableAt ℝ (f n) x := by
    exact ae_all_iff.2 fun n => (hf_ac n).ae_differentiableAt
  filter_upwards [h_all] with x hx hxi
  exact fun n => hx n (by simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hxi)

theorem apm_a94a02
    (f : ℕ → ℝ → ℝ)
    (hf_monotone : ∀ n, MonotoneOn (f n) (Icc (0 : ℝ) 1))
    (hf_ac : ∀ n, AbsolutelyContinuousOnInterval (f n) 0 1)
    (hf_nonnegative : ∀ n x, x ∈ Icc (0 : ℝ) 1 → 0 ≤ f n x)
    (hf_sum : Summable (fun n ↦ f n 1)) :
    (∫⁻ x in Icc (0 : ℝ) 1, apmDerivativeSeries f x ∂volume) < ⊤ ∧
      (∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
        apmDerivativeSeries f x < ⊤) ∧
      (∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)),
        ENNReal.ofReal (deriv (apmFunctionSeries f) x) =
          apmDerivativeSeries f x) := by
  let clamp : ℝ → ℝ := fun x => max 0 (min 1 x)
  let F : ℕ → ℝ → ℝ := fun n x => f n (clamp x)
  have hclamp_mem (x : ℝ) : clamp x ∈ Icc (0 : ℝ) 1 := by
    dsimp [clamp]
    constructor <;> simp
  have hclamp_mono : Monotone clamp := by
    intro x y hxy
    dsimp [clamp]
    exact max_le_max (le_refl (0 : ℝ)) (min_le_min (le_refl (1 : ℝ)) hxy)
  have hF_mono (n : ℕ) : Monotone (F n) := by
    intro x y hxy
    exact hf_monotone n (hclamp_mem x) (hclamp_mem y) (hclamp_mono hxy)
  have hF_summable (x : ℝ) : Summable (fun n => F n x) := by
    apply Summable.of_norm_bounded hf_sum
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonnegative n _ (hclamp_mem x))]
    exact hf_monotone n (hclamp_mem x) (by norm_num) (hclamp_mem x).2
  have hF_deriv := APM.deriv_sum_of_monotone_ae
      (APM.pointwiseSum F) F hF_mono hF_summable (fun _ => rfl)
  have h_interior : ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), x ∈ Ioo (0 : ℝ) 1 := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(volume : Measure ℝ).ae_ne 0, (volume : Measure ℝ).ae_ne 1]
      with x hx0 hx1 hmem
    exact ⟨lt_of_le_of_ne hmem.1 (Ne.symm hx0), lt_of_le_of_ne hmem.2 hx1⟩
  have hderiv_nonneg (n : ℕ) :
      ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), 0 ≤ deriv (f n) x := by
    filter_upwards [h_interior] with x hx
    have heq : F n =ᶠ[nhds x] f n := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp [F, clamp, hy.1.le, hy.2.le]
    rw [← heq.deriv_eq]
    exact (hF_mono n).deriv_nonneg
  have hderiv_nonneg_all :
      ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ n, 0 ≤ deriv (f n) x :=
    ae_all_iff.2 hderiv_nonneg
  have hterm_integral (n : ℕ) :
      ∫⁻ x in Icc (0 : ℝ) 1, ENNReal.ofReal (deriv (f n) x) ∂volume =
        ENNReal.ofReal (f n 1 - f n 0) := by
    have hi : Integrable (deriv (f n)) (volume.restrict (Icc (0 : ℝ) 1)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).1
        (hf_ac n).intervalIntegrable_deriv
    rw [← ofReal_integral_eq_lintegral_ofReal hi (hderiv_nonneg n),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
      (hf_ac n).integral_deriv_eq_sub]
  have hdiff_summable : Summable (fun n => f n 1 - f n 0) := by
    apply Summable.of_norm_bounded hf_sum
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact sub_le_self _ (hf_nonnegative n 0 (by norm_num))
    · exact sub_nonneg.mpr (hf_monotone n (by norm_num) (by norm_num) (by norm_num))
  have hg_eq : apmDerivativeSeries f =ᵐ[volume.restrict (Icc (0 : ℝ) 1)]
      fun x => ∑' n, ENNReal.ofReal (deriv (f n) x) := by
    filter_upwards [apm_a94a02_ae_all_differentiable f hf_ac] with x hx
    simp [apmDerivativeSeries, hx]
  have hlintegral :
      (∫⁻ x in Icc (0 : ℝ) 1, apmDerivativeSeries f x ∂volume) =
        ENNReal.ofReal (∑' n, (f n 1 - f n 0)) := by
    rw [lintegral_congr_ae hg_eq, lintegral_tsum]
    · simp_rw [hterm_integral]
      exact (ENNReal.ofReal_tsum_of_nonneg
        (fun n => sub_nonneg.mpr (hf_monotone n (by norm_num) (by norm_num) (by norm_num)))
        hdiff_summable).symm
    · intro n
      exact (measurable_deriv (f n)).ennreal_ofReal.aemeasurable
  have hg_int : (∫⁻ x in Icc (0 : ℝ) 1, apmDerivativeSeries f x ∂volume) < ⊤ := by
    rw [hlintegral]
    exact ENNReal.ofReal_lt_top
  refine ⟨hg_int, ?_, ?_⟩
  · apply ae_lt_top'
    · apply AEMeasurable.congr _ hg_eq.symm
      fun_prop
    · exact hg_int.ne
  · have hF_deriv_restrict :=
      ae_restrict_of_ae (s := Icc (0 : ℝ) 1) hF_deriv
    have hg_finite :
        ∀ᵐ x ∂(volume.restrict (Icc (0 : ℝ) 1)), apmDerivativeSeries f x < ⊤ := by
      apply ae_lt_top'
      · apply AEMeasurable.congr _ hg_eq.symm
        fun_prop
      · exact hg_int.ne
    filter_upwards [h_interior, hF_deriv_restrict, hg_eq, hg_finite,
      hderiv_nonneg_all] with x hx hseries hgx hgfin hnonneg
    have hterm_local (n : ℕ) : F n =ᶠ[nhds x] f n := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp [F, clamp, hy.1.le, hy.2.le]
    have hsum_local : APM.pointwiseSum F =ᶠ[nhds x] apmFunctionSeries f := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      simp [APM.pointwiseSum, apmFunctionSeries, F, clamp, hy.1.le, hy.2.le]
    have hreal : deriv (apmFunctionSeries f) x = ∑' n, deriv (f n) x := by
      rw [← hsum_local.deriv_eq, hseries]
      apply tsum_congr
      intro n
      exact (hterm_local n).deriv_eq
    have htsum : (∑' n, ENNReal.ofReal (deriv (f n) x)) ≠ ⊤ := by
      rw [← hgx]
      exact hgfin.ne
    have hsummable_real : Summable (fun n => deriv (f n) x) := by
      have hs := ENNReal.summable_toReal htsum
      simpa only [ENNReal.toReal_ofReal (hnonneg _)] using hs
    rw [hreal, ENNReal.ofReal_tsum_of_nonneg hnonneg hsummable_real]
    exact hgx.symm
