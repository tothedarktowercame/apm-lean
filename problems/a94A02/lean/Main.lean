import Mathlib
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

open MeasureTheory Set Function Filter

noncomputable section

/-! Local infrastructure for differentiating pointwise-convergent series of
monotone functions.  Kept here so this problem remains independently checkable. -/
namespace APM

open scoped Topology

/-- Pointwise sum of the monotone sequence of maps. -/
def pointwiseSum (fns : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, fns n x

/-- Pointwise sum of the derivatives. -/
def derivativeSum (fns : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, deriv (fun y => fns n y) x

/-- A pointwise-convergent series of monotone real functions is monotone. -/
lemma pointwiseSum_monotone
    (fns : ℕ → ℝ → ℝ) (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x) :
    Monotone (pointwiseSum fns) := by
  intro x y hxy
  exact (hsummable x).tsum_le_tsum (fun n => hmono n hxy) (hsummable y)

/-- Part (1): the derivative of the series exists a.e. and equals the sum of derivatives. -/
theorem deriv_sum_of_monotone
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    ∀ᵐ x ∂volume, HasDerivAt f (derivativeSum fns x) x := by
  let μs : ℕ → Measure ℝ := fun n => (hmono n).stieltjesFunction.measure
  have hfmono : Monotone f := by
    intro x y hxy
    rw [hf x, hf y]
    exact pointwiseSum_monotone fns hmono hsummable hxy
  have hright (x : ℝ) :
      Summable (fun n => rightLim (fns n) x) ∧
        rightLim f x = ∑' n, rightLim (fns n) x := by
    let B : ℕ → ℝ := fun n => fns n (x + 1) - fns n x
    have hB : Summable B := (hsummable (x + 1)).sub (hsummable x)
    have hlim (n : ℕ) :
        Tendsto (fun y => fns n y - fns n x) (nhdsWithin x (Ioi x))
          (nhds (rightLim (fns n) x - fns n x)) :=
      ((hmono n).tendsto_rightLim x).sub_const _
    have hbound : ∀ᶠ y in nhdsWithin x (Ioi x),
        ∀ n, ‖fns n y - fns n x‖ ≤ B n := by
      filter_upwards [Ioo_mem_nhdsGT (show x < x + 1 by linarith)] with y hy
      intro n
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (hmono n hy.1.le))]
      exact sub_le_sub_right (hmono n hy.2.le) _
    have hT := tendsto_tsum_of_dominated_convergence hB hlim hbound
    have hsum_eq (y : ℝ) :
        (∑' n, (fns n y - fns n x)) = f y - f x := by
      rw [(hsummable y).tsum_sub (hsummable x), ← pointwiseSum, ← pointwiseSum,
        ← hf y, ← hf x]
    have hrightdiff :
        rightLim f x - f x = ∑' n, (rightLim (fns n) x - fns n x) := by
      apply tendsto_nhds_unique ((hfmono.tendsto_rightLim x).sub_const _)
      exact hT.congr' (Eventually.of_forall fun y => hsum_eq y)
    have hjump_nonneg (n : ℕ) : 0 ≤ rightLim (fns n) x - fns n x :=
      sub_nonneg.mpr ((hmono n).le_rightLim le_rfl)
    have hjump_le (n : ℕ) : rightLim (fns n) x - fns n x ≤ B n := by
      dsimp [B]
      exact sub_le_sub_right ((hmono n).rightLim_le (by linarith)) _
    have hjump_sum : Summable (fun n => rightLim (fns n) x - fns n x) :=
      Summable.of_nonneg_of_le hjump_nonneg hjump_le hB
    constructor
    · have := (hsummable x).add hjump_sum
      simpa only [add_sub_cancel] using this
    · calc
        rightLim f x = f x + (rightLim f x - f x) := by
          ring
        _ = (∑' n, fns n x) + ∑' n, (rightLim (fns n) x - fns n x) := by
          rw [← pointwiseSum, ← hf x, hrightdiff]
        _ = ∑' n, (fns n x + (rightLim (fns n) x - fns n x)) := by
          rw [(hsummable x).tsum_add hjump_sum]
        _ = ∑' n, rightLim (fns n) x := by
          apply tsum_congr
          intro n
          ring
  have hmeasure : hfmono.stieltjesFunction.measure = Measure.sum μs := by
    apply Measure.ext_of_Ioc
    intro a b hab
    rw [StieltjesFunction.measure_Ioc, Measure.sum_apply _ measurableSet_Ioc]
    simp_rw [μs, StieltjesFunction.measure_Ioc, Monotone.stieltjesFunction_eq]
    rw [← ENNReal.ofReal_tsum_of_nonneg]
    · congr 1
      rw [hright b |>.2, hright a |>.2, (hright b |>.1).tsum_sub (hright a |>.1)]
    · intro n
      exact sub_nonneg.mpr ((hmono n).rightLim hab.le)
    · exact (hright b |>.1).sub (hright a |>.1)
  let s : Measure ℝ := Measure.sum fun n => (μs n).singularPart volume
  let d : ℝ → ENNReal := fun x => ∑' n, (μs n).rnDeriv volume x
  have hd_meas : Measurable d := by
    dsimp [d]
    fun_prop
  have hs_sing : s ⟂ₘ volume := by
    dsimp [s]
    exact Measure.MutuallySingular.sum_left.2 fun n =>
      Measure.mutuallySingular_singularPart _ _
  have hdecomp : Measure.sum μs = s + volume.withDensity d := by
    dsimp [s, d]
    symm
    have hdsum : Summable (fun n => (μs n).rnDeriv volume) :=
      Pi.summable.2 fun _ => ENNReal.summable
    rw [show (fun x => ∑' n, (μs n).rnDeriv volume x) =
        ∑' n, (μs n).rnDeriv volume by
      funext x
      exact (tsum_apply hdsum).symm]
    rw [withDensity_tsum (fun n => Measure.measurable_rnDeriv (μs n) volume),
      Measure.sum_add_sum]
    congr 1
    funext n
    exact Measure.singularPart_add_rnDeriv (μs n) volume
  have hd_rn : d =ᵐ[volume] (Measure.sum μs).rnDeriv volume :=
    Measure.eq_rnDeriv hd_meas hs_sing hdecomp
  have hd_rn_f : d =ᵐ[volume] hfmono.stieltjesFunction.measure.rnDeriv volume := by
    simpa only [hmeasure] using hd_rn
  have hsum_finite : ∀ᵐ x ∂volume, d x ≠ ⊤ := by
    filter_upwards [hd_rn_f,
      Measure.rnDeriv_lt_top hfmono.stieltjesFunction.measure volume] with x hx hxtop
    exact hx.trans_ne hxtop.ne
  have hterms_finite : ∀ᵐ x ∂volume, ∀ n, (μs n).rnDeriv volume x ≠ ⊤ := by
    apply ae_all_iff.2
    intro n
    exact Measure.rnDeriv_lt_top (μs n) volume |>.mono fun x hx => hx.ne
  have hf_deriv := hfmono.ae_hasDerivAt
  have hfns_deriv : ∀ᵐ x ∂volume, ∀ n,
      HasDerivAt (fns n) ((μs n).rnDeriv volume x).toReal x := by
    apply ae_all_iff.2
    intro n
    simpa [μs] using (hmono n).ae_hasDerivAt
  filter_upwards [hf_deriv, hfns_deriv, hd_rn_f, hsum_finite, hterms_finite]
    with x hfx hfnx hdrn hdfin htermfin
  have hd_real : (hfmono.stieltjesFunction.measure.rnDeriv volume x).toReal =
      ∑' n, ((μs n).rnDeriv volume x).toReal := by
    rw [← hdrn, show d x = ∑' n, (μs n).rnDeriv volume x by rfl,
      ENNReal.tsum_toReal_eq htermfin]
  rw [derivativeSum, tsum_congr fun n => (hfnx n).deriv, ← hd_real]
  exact hfx

/-- Part (2): convert the `HasDerivAt` statement into an equality of classical derivatives a.e. -/
theorem deriv_sum_of_monotone_ae
    (f : ℝ → ℝ) (fns : ℕ → ℝ → ℝ)
    (hmono : ∀ n, Monotone (fns n))
    (hsummable : ∀ x, Summable fun n => fns n x)
    (hf : ∀ x, f x = pointwiseSum fns x) :
    deriv f =ᵐ[volume] derivativeSum fns := by
  filter_upwards [deriv_sum_of_monotone f fns hmono hsummable hf] with x hx
  exact hx.deriv

end APM

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
