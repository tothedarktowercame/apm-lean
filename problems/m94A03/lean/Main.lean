import Mathlib
import ConstructionTargets.RadialIntegrationR3

/-!
# APM m94A03

## Statement repairs

None.

## Encoding notes

The ambient space is the genuine Euclidean space `ℝⁿ`.  Sobolev membership is
encoded from first principles using `L²` membership and an `L²` weak gradient,
tested against smooth compactly supported scalar functions on the unit ball.
The totalized value `Real.log 0 = 0` only chooses a representative at the
measure-zero singular point.
-/

open Filter MeasureTheory Set
open scoped ContDiff ENNReal

noncomputable def apm_m94a03_logNorm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.log ‖x‖

/-- The classical gradient of `log ‖x‖`, totalized at the origin. -/
noncomputable def apm_m94a03_logNormGradient {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ‖x‖⁻¹ ^ 2 • x

/-- A smooth regularization of `log ‖x‖`, used to cross the singular origin
without introducing an artificial inner boundary. -/
noncomputable def apm_m94a03_logNormRegularized {n : ℕ} (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (2 : ℝ)⁻¹ * Real.log (‖x‖ ^ 2 + ε)

/-- The regularized logarithm has the expected derivative everywhere when
the regularization parameter is positive. -/
lemma apm_m94a03_hasFDerivAt_logNormRegularized {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (x : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (apm_m94a03_logNormRegularized ε)
      ((‖x‖ ^ 2 + ε)⁻¹ • (innerSL ℝ x)) x := by
  have harg : ‖x‖ ^ 2 + ε ≠ 0 := by positivity
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const ε).log harg
  have h' := h.const_mul ((2 : ℝ)⁻¹)
  convert h' using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 2000000 in
/-- Smooth integration by parts before sending the regularization parameter
to zero.  All three dimensions in the problem share this identity. -/
lemma apm_m94a03_integral_logNormRegularized_mul_fderiv {n : ℕ} {ε : ℝ}
    (hε : 0 < ε) (i : Fin n)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ∫ x, apm_m94a03_logNormRegularized ε x *
        fderiv ℝ φ x (EuclideanSpace.single i 1) =
      -∫ x, ((‖x‖ ^ 2 + ε)⁻¹ * x i) * φ x := by
  have hf : Differentiable ℝ
      (apm_m94a03_logNormRegularized ε :
        EuclideanSpace ℝ (Fin n) → ℝ) :=
    fun x ↦ (apm_m94a03_hasFDerivAt_logNormRegularized hε x).differentiableAt
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hfcont : Continuous
      (apm_m94a03_logNormRegularized ε :
        EuclideanSpace ℝ (Fin n) → ℝ) := by
    unfold apm_m94a03_logNormRegularized
    exact continuous_const.mul
      (((continuous_norm.pow 2).add continuous_const).log (fun x ↦
        ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) hε)))
  have hregder :
      (fun x ↦ fderiv ℝ (apm_m94a03_logNormRegularized ε) x
        (EuclideanSpace.single i 1)) =
      (fun x ↦ (‖x‖ ^ 2 + ε)⁻¹ * x i) := by
    funext x
    rw [(apm_m94a03_hasFDerivAt_logNormRegularized hε x).fderiv]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
    rw [PiLp.inner_apply, Finset.sum_eq_single i]
    · simp [PiLp.single_apply, real_inner_comm, real_inner_eq_re_inner]
    · intro j _ hji
      simp [PiLp.single_apply, hji]
    · simp
  have hregdercont : Continuous
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (‖x‖ ^ 2 + ε)⁻¹ * x i) := by
    exact (((continuous_norm.pow 2).add continuous_const).inv₀
      (fun x ↦ ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) hε))).mul
        (EuclideanSpace.proj i).continuous
  have hφdercont : Continuous
      (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    ((hφ.fderiv_right (m := 0) (by simp)).clm_apply contDiff_const).continuous
  have hφderc : HasCompactSupport
      (fun x ↦ fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    simpa [Function.comp_def] using
      (hφc.fderiv ℝ).comp_left
        (g := fun L ↦ L (EuclideanSpace.single i 1)) (by simp)
  have hint1 : Integrable (fun x ↦
      ((‖x‖ ^ 2 + ε)⁻¹ * x i) * φ x) :=
    (hregdercont.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hint1' : Integrable (fun x ↦
      fderiv ℝ (apm_m94a03_logNormRegularized ε) x
        (EuclideanSpace.single i 1) * φ x) := by
    apply hint1.congr
    filter_upwards with x
    rw [congrFun hregder x]
  have hint2 : Integrable (fun x ↦ apm_m94a03_logNormRegularized ε x *
      fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hfcont.mul hφdercont).integrable_of_hasCompactSupport
      hφderc.mul_left
  have hint3 : Integrable (fun x ↦
      apm_m94a03_logNormRegularized ε x * φ x) :=
    (hfcont.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
  have hip :
      ∫ x, apm_m94a03_logNormRegularized ε x *
          fderiv ℝ φ x (EuclideanSpace.single i 1) =
        -∫ x, fderiv ℝ (apm_m94a03_logNormRegularized ε) x
          (EuclideanSpace.single i 1) * φ x := by
    apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    · exact hint1'
    · exact hint2
    · exact hint3
    · exact fun x _ ↦ hf x
    · exact fun x _ ↦ hφd x
  rw [hip]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [congrFun hregder x]

/-- The concrete regularization scale used for dominated convergence is
strictly positive. -/
lemma apm_m94a03_regularizationScale_pos (k : ℕ) :
    0 < (1 / ((k : ℝ) + 1) : ℝ) := by positivity

/-- Away from the null singular point, the smooth logarithms converge to the
totalized logarithmic representative. -/
lemma apm_m94a03_logNormRegularized_tendsto {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    Tendsto (fun k : ℕ ↦
      apm_m94a03_logNormRegularized (1 / ((k : ℝ) + 1)) x)
      atTop (nhds (apm_m94a03_logNorm x)) := by
  have heps : Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1) : ℝ))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have harg : Tendsto (fun k : ℕ ↦ ‖x‖ ^ 2 + 1 / ((k : ℝ) + 1))
      atTop (nhds (‖x‖ ^ 2)) := by
    convert (tendsto_const_nhds.add heps) using 1 <;> simp
  have hsq : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hlog := (Real.continuousAt_log hsq).tendsto.comp harg
  have hhalf : Tendsto (fun _ : ℕ ↦ (2 : ℝ)⁻¹) atTop
      (nhds (2 : ℝ)⁻¹) := tendsto_const_nhds
  simpa [apm_m94a03_logNormRegularized, apm_m94a03_logNorm,
    Real.log_pow, norm_ne_zero_iff.mpr hx] using
    (hhalf.mul hlog)

/-- The coordinate derivatives of the smooth regularizations converge to the
classical gradient candidate away from the origin. -/
lemma apm_m94a03_logNormRegularizedGradient_tendsto {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (i : Fin n) :
    Tendsto (fun k : ℕ ↦
      (‖x‖ ^ 2 + 1 / ((k : ℝ) + 1))⁻¹ * x i) atTop
      (nhds (apm_m94a03_logNormGradient x i)) := by
  have heps : Tendsto (fun k : ℕ ↦ (1 / ((k : ℝ) + 1) : ℝ))
      atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have harg : Tendsto (fun k : ℕ ↦ ‖x‖ ^ 2 + 1 / ((k : ℝ) + 1))
      atTop (nhds (‖x‖ ^ 2)) := by
    convert (tendsto_const_nhds.add heps) using 1 <;> simp
  have hsq : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hinv := harg.inv₀ hsq
  simpa [apm_m94a03_logNormGradient, PiLp.smul_apply, smul_eq_mul] using
    hinv.mul_const (x i)

/-- Every regularized gradient coordinate is dominated by inverse radius,
uniformly in the positive regularization parameter. -/
lemma apm_m94a03_abs_regularizedGradient_le_invNorm {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (i : Fin n) :
    |(‖x‖ ^ 2 + ε)⁻¹ * x i| ≤ ‖x‖⁻¹ := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxi : |x i| ≤ ‖x‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  rw [abs_mul, abs_inv, abs_of_nonneg (add_nonneg (sq_nonneg _) hε)]
  have hden : 0 < ‖x‖ ^ 2 + ε := add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) hε
  rw [inv_mul_le_iff₀ hden, inv_eq_one_div]
  field_simp
  nlinarith

/-- Dominated convergence for the gradient side of the regularized
integration-by-parts identity. The only analytic input is local integrability
of inverse radius on the chosen measurable domain. -/
lemma apm_m94a03_integral_regularizedGradient_tendsto {n : ℕ}
    (hn : 0 < n) (s : Set (EuclideanSpace ℝ (Fin n))) (hs : MeasurableSet s)
    (hinv : Integrable (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖⁻¹)
      (volume.restrict s)) (i : Fin n)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    Tendsto (fun k : ℕ ↦ ∫ x,
      ((‖x‖ ^ 2 + 1 / ((k : ℝ) + 1))⁻¹ * x i) * φ x
        ∂(volume.restrict s)) atTop
      (nhds (∫ x, apm_m94a03_logNormGradient x i * φ x
        ∂(volume.restrict s))) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ ‖x‖⁻¹ * |φ x|
  have hb : Integrable b (volume.restrict s) := by
    have hφtop : MemLp φ ⊤ (volume.restrict s) :=
      hφ.continuous.memLp_top_of_hasCompactSupport hφc _
    have hmul := hinv.mul_of_top_right hφtop
    apply hmul.norm.congr
    filter_upwards with x
    simp [b, Real.norm_eq_abs, abs_mul, mul_comm,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  apply tendsto_integral_of_dominated_convergence b
  · intro k
    apply Continuous.aestronglyMeasurable
    have heps : 0 < (1 / ((k : ℝ) + 1) : ℝ) :=
      apm_m94a03_regularizationScale_pos k
    exact (((continuous_norm.pow 2).add continuous_const).inv₀
      (fun x ↦ ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) heps))).mul
        (EuclideanSpace.proj i).continuous |>.mul hφ.continuous
  · exact hb
  · intro k
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin n)))]
      with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (apm_m94a03_abs_regularizedGradient_le_invNorm hx
        (le_of_lt (apm_m94a03_regularizationScale_pos k)) i) (abs_nonneg _)
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne
      (0 : EuclideanSpace ℝ (Fin n)))] with x hx
    exact (apm_m94a03_logNormRegularizedGradient_tendsto hx i).mul_const (φ x)

/-- On the unit ball, every regularized logarithm in the chosen sequence is
dominated away from the null origin by `|log ‖x‖|` plus a fixed constant. -/
lemma apm_m94a03_abs_logNormRegularized_le {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (hxball : ‖x‖ < 1)
    (k : ℕ) :
    |apm_m94a03_logNormRegularized (1 / ((k : ℝ) + 1)) x| ≤
      |apm_m94a03_logNorm x| + |(2 : ℝ)⁻¹ * Real.log 2| := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have heps0 : 0 ≤ (1 / ((k : ℝ) + 1) : ℝ) :=
    (apm_m94a03_regularizationScale_pos k).le
  have heps1 : (1 / ((k : ℝ) + 1) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    norm_num
  have harg0 : 0 < ‖x‖ ^ 2 + 1 / ((k : ℝ) + 1) :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) heps0
  have harg2 : ‖x‖ ^ 2 + 1 / ((k : ℝ) + 1) ≤ 2 := by
    nlinarith [sq_nonneg (‖x‖ - 1)]
  have hlower : Real.log (‖x‖ ^ 2) ≤
      Real.log (‖x‖ ^ 2 + 1 / ((k : ℝ) + 1)) :=
    Real.strictMonoOn_log.monotoneOn (sq_pos_of_pos hr)
      harg0 (le_add_of_nonneg_right heps0)
  have hupper : Real.log (‖x‖ ^ 2 + 1 / ((k : ℝ) + 1)) ≤
      Real.log 2 :=
    Real.strictMonoOn_log.monotoneOn harg0 (by norm_num) harg2
  have hlogr : Real.log ‖x‖ ≤ 0 := Real.log_nonpos hr.le hxball.le
  have hc : 0 ≤ (2 : ℝ)⁻¹ * Real.log 2 :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  rw [apm_m94a03_logNormRegularized, apm_m94a03_logNorm,
    abs_le, abs_of_nonpos hlogr, abs_of_nonneg hc]
  rw [Real.log_pow] at hlower
  constructor <;> nlinarith

/-- Dominated convergence for the logarithm side on a unit ball, using the
`L²` membership already available in dimensions three and four (and obtainable
by the same radial estimate in dimension two). -/
lemma apm_m94a03_integral_logNormRegularized_tendsto {n : ℕ}
    (hn : 0 < n)
    (hlog : MemLp (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin n) → ℝ) 1
      (volume.restrict (Metric.ball 0 1)))
    (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Tendsto (fun k : ℕ ↦ ∫ x,
      apm_m94a03_logNormRegularized (1 / ((k : ℝ) + 1)) x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)
        ∂(volume.restrict (Metric.ball 0 1))) atTop
      (nhds (∫ x, apm_m94a03_logNorm x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)
        ∂(volume.restrict (Metric.ball 0 1)))) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    volume.restrict (Metric.ball 0 1)
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    fderiv ℝ φ x (EuclideanSpace.single i 1)
  let c : ℝ := |(2 : ℝ)⁻¹ * Real.log 2|
  let b : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    (|apm_m94a03_logNorm x| + c) * |q x|
  letI : IsFiniteMeasure μ := IsFiniteMeasure.mk (by
    simpa [μ] using (measure_ball_lt_top
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (x := (0 : EuclideanSpace ℝ (Fin n))) (r := (1 : ℝ))))
  have hlog1 : Integrable apm_m94a03_logNorm μ := hlog.integrable (by norm_num)
  have hbase : Integrable (fun x ↦ |apm_m94a03_logNorm x| + c) μ :=
    hlog1.norm.add (integrable_const c)
  have hqdiff : ContDiff ℝ 0 q :=
    (hφ.fderiv_right (m := 0) (by simp)).clm_apply contDiff_const
  have hqc : HasCompactSupport q := by
    simpa [q, Function.comp_def] using
      (hφc.fderiv ℝ).comp_left
        (g := fun L ↦ L (EuclideanSpace.single i 1)) (by simp)
  have hqtop : MemLp q ⊤ μ :=
    hqdiff.continuous.memLp_top_of_hasCompactSupport hqc _
  have hb : Integrable b μ := by
    have hm := hbase.mul_of_top_right hqtop
    apply hm.norm.congr
    filter_upwards with x
    simp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (show 0 ≤ |apm_m94a03_logNorm x| + c from
      add_nonneg (abs_nonneg _) (abs_nonneg _))]
    simp [b, q, c, mul_comm]
  apply tendsto_integral_of_dominated_convergence b
  · intro k
    exact ((by
      have heps := apm_m94a03_regularizationScale_pos k
      exact continuous_const.mul
        (((continuous_norm.pow 2).add continuous_const).log (fun x ↦
          ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) heps))) :
      Continuous (apm_m94a03_logNormRegularized (1 / ((k : ℝ) + 1)) :
        EuclideanSpace ℝ (Fin n) → ℝ))).mul hqdiff.continuous |>.aestronglyMeasurable
  · exact hb
  · intro k
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : EuclideanSpace ℝ (Fin n)))] with x hxb hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (apm_m94a03_abs_logNormRegularized_le hx
        (by simpa [Metric.mem_ball] using hxb) k) (abs_nonneg _)
  · filter_upwards [ae_restrict_of_ae (volume.ae_ne
      (0 : EuclideanSpace ℝ (Fin n)))] with x hx
    exact (apm_m94a03_logNormRegularized_tendsto hx).mul_const (q x)

/-- Away from the origin, the totalized logarithm has the expected Fréchet
derivative.  Writing it as one half of `log ‖x‖²` avoids a separate derivative
theorem for the norm. -/
lemma apm_m94a03_hasFDerivAt_logNorm {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HasFDerivAt apm_m94a03_logNorm
      (‖x‖⁻¹ ^ 2 • (innerSL ℝ x)) x := by
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hsquared : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hnorm
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.log hsquared).const_mul
    ((2 : ℝ)⁻¹)
  have heq : apm_m94a03_logNorm =ᶠ[nhds x]
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (2 : ℝ)⁻¹ * Real.log (‖y‖ ^ 2)) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [apm_m94a03_logNorm, Real.log_pow]
    ring
  convert h.congr_of_eventuallyEq heq using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

/-- Each directional derivative in the standard coordinate basis agrees with
the corresponding component of the classical gradient candidate. -/
lemma apm_m94a03_fderiv_logNorm_single {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ apm_m94a03_logNorm x (EuclideanSpace.single i 1) =
      apm_m94a03_logNormGradient x i := by
  rw [(apm_m94a03_hasFDerivAt_logNorm hx).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply,
    apm_m94a03_logNormGradient, PiLp.smul_apply]
  rw [PiLp.inner_apply]
  rw [Finset.sum_eq_single i]
  · apply congrArg (fun z : ℝ => ‖x‖⁻¹ ^ 2 • z)
    rw [real_inner_comm]
    rw [real_inner_eq_re_inner ℝ]
    simp [PiLp.single_apply]
  · intro j _ hji
    simp [PiLp.single_apply, hji]
  · simp

/-- The coordinate derivative formula is valid almost everywhere for every
restriction of Euclidean volume, including the unit ball measure used below. -/
lemma apm_m94a03_fderiv_logNorm_single_ae {n : ℕ}
    (hn : 0 < n) (s : Set (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    ∀ᵐ x ∂(volume.restrict s),
      fderiv ℝ apm_m94a03_logNorm x (EuclideanSpace.single i 1) =
        apm_m94a03_logNormGradient x i := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hne : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), x ≠ 0 :=
    volume.ae_ne 0
  filter_upwards [ae_restrict_of_ae hne] with x hx
  exact apm_m94a03_fderiv_logNorm_single hx i

lemma apm_m94a03_norm_logNormGradient {n : ℕ}
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ‖apm_m94a03_logNormGradient x‖ = ‖x‖⁻¹ := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [apm_m94a03_logNormGradient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  field_simp

/-- The norm formula also holds at the totalized origin, where both sides are
zero. This removes the exceptional point from later `L²` calculations. -/
lemma apm_m94a03_norm_logNormGradient_all {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖apm_m94a03_logNormGradient x‖ = ‖x‖⁻¹ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [apm_m94a03_logNormGradient]
  · exact apm_m94a03_norm_logNormGradient hx

/-- The totalized logarithmic representative is strongly measurable. -/
lemma apm_m94a03_logNorm_aestronglyMeasurable {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} :
    AEStronglyMeasurable
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin n) → ℝ) μ := by
  exact (Real.measurable_log.comp measurable_norm).aestronglyMeasurable

/-- The totalized classical gradient is strongly measurable. -/
lemma apm_m94a03_logNormGradient_aestronglyMeasurable {n : ℕ}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} :
    AEStronglyMeasurable
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) μ := by
  apply Measurable.aestronglyMeasurable
  exact ((measurable_norm.inv.pow_const 2).smul measurable_id)

/-- Square-integrability (indeed `Lᵖ` membership for any exponent) of the
vector candidate is exactly the scalar radial integrability problem. -/
lemma apm_m94a03_logNormGradient_memLp_iff {n : ℕ} {p : ℝ≥0∞}
    {μ : Measure (EuclideanSpace ℝ (Fin n))} :
    MemLp (apm_m94a03_logNormGradient :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) p μ ↔
      MemLp (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖⁻¹) p μ := by
  apply memLp_congr_norm
  · exact apm_m94a03_logNormGradient_aestronglyMeasurable
  · exact measurable_norm.inv.aestronglyMeasurable
  · filter_upwards with x
    rw [apm_m94a03_norm_logNormGradient_all, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]

/-- In dimension three the scalar inverse-radius singularity is square
integrable on the unit ball. This specializes the repository's proved radial
integration theorem; its radial density is simply the indicator of `(0,1)`. -/
lemma apm_m94a03_invNorm_memLp_two_ball_fin_three :
    MemLp (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖⁻¹) 2
      (volume.restrict (Metric.ball 0 1)) := by
  rw [← memLp_indicator_iff_restrict measurableSet_ball]
  let g : ℝ → ℝ := fun r ↦ if 0 < r ∧ r < 1 then r⁻¹ else 0
  have hfun :
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator
          (fun x => ‖x‖⁻¹) =
        fun x => g ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [g]
    · by_cases hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
      · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [Set.indicator_apply, hball, g, norm_pos_iff.mpr hx, hlt]
      · have hnorm : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [Set.indicator_apply, hball, g, hnorm]
  rw [hfun, ConstructionTargets.RadialIntegrationR3.memLp_radial_R3_iff]
  · have hdensity :
        (fun r : ℝ => r ^ 2 * ‖g r‖ ^ (2 : ℝ≥0∞).toReal) =
          (Set.Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) := by
      funext r
      by_cases hr0 : 0 < r
      · by_cases hr1 : r < 1
        · simp [g, hr0, hr1, Real.norm_eq_abs, abs_of_pos hr0]
          field_simp
        · simp [g, hr0, hr1]
      · have hrI : r ∉ Set.Ioo (0 : ℝ) 1 := fun hr ↦ hr0 hr.1
        simp [g, hr0, hrI]
    rw [hdensity]
    exact ((integrableOn_const (s := Set.Ioo (0 : ℝ) 1)
      (measure_Ioo_lt_top.ne)).integrable_indicator
      measurableSet_Ioo).integrableOn
  · rw [← hfun]
    exact (measurable_norm.inv.indicator measurableSet_ball).aestronglyMeasurable
  · norm_num
  · norm_num

/-- Consequently the actual vector-valued classical gradient candidate is in
`L²` on the three-dimensional unit ball. -/
lemma apm_m94a03_logNormGradient_memLp_two_ball_fin_three :
    MemLp (apm_m94a03_logNormGradient :
      EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) 2
      (volume.restrict (Metric.ball 0 1)) := by
  rw [apm_m94a03_logNormGradient_memLp_iff]
  exact apm_m94a03_invNorm_memLp_two_ball_fin_three

/-- The general polar decomposition specialized to Euclidean four-space. -/
lemma apm_m94a03_memLp_radial_R4_iff {g : ℝ → ℝ} {p : ℝ≥0∞}
    (hg : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 4) => g ‖x‖) volume)
    (hp0 : p ≠ 0) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    MemLp (fun x : EuclideanSpace ℝ (Fin 4) => g ‖x‖) p volume ↔
      IntegrableOn (fun r : ℝ => r ^ 3 * ‖g r‖ ^ p.toReal) (Ioi 0) := by
  rw [← integrable_norm_rpow_iff hg hp0 hp_top]
  simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    smul_eq_mul] using
    (MeasureTheory.integrable_fun_norm_addHaar
      (volume : Measure (EuclideanSpace ℝ (Fin 4)))
      (f := fun r : ℝ => ‖g r‖ ^ p.toReal))

/-- In four dimensions the inverse-radius candidate is square integrable on
the unit ball. -/
lemma apm_m94a03_invNorm_memLp_two_ball_fin_four :
    MemLp (fun x : EuclideanSpace ℝ (Fin 4) => ‖x‖⁻¹) 2
      (volume.restrict (Metric.ball 0 1)) := by
  rw [← memLp_indicator_iff_restrict measurableSet_ball]
  let g : ℝ → ℝ := fun r ↦ if 0 < r ∧ r < 1 then r⁻¹ else 0
  have hfun :
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1).indicator
          (fun x => ‖x‖⁻¹) = fun x => g ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [g]
    · by_cases hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1
      · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, norm_pos_iff.mpr hx, hlt]
      · have hnorm : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, hnorm]
  rw [hfun, apm_m94a03_memLp_radial_R4_iff]
  · have hdensity :
        (fun r : ℝ => r ^ 3 * ‖g r‖ ^ (2 : ℝ≥0∞).toReal) =
          (Set.Ioo (0 : ℝ) 1).indicator (fun r ↦ r) := by
      funext r
      by_cases hr0 : 0 < r
      · by_cases hr1 : r < 1
        · simp [g, hr0, hr1, Real.norm_eq_abs, abs_of_pos hr0]
          field_simp
        · simp [g, hr0, hr1]
      · have hrI : r ∉ Set.Ioo (0 : ℝ) 1 := fun hr ↦ hr0 hr.1
        simp [g, hr0, hrI]
    rw [hdensity]
    have hrint : IntegrableOn (fun r : ℝ ↦ r) (Set.Ioo 0 1) :=
      (continuousOn_id.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set
        Ioo_subset_Icc_self
    exact (hrint.integrable_indicator measurableSet_Ioo).integrableOn
  · rw [← hfun]
    exact (measurable_norm.inv.indicator measurableSet_ball).aestronglyMeasurable
  · norm_num
  · norm_num

/-- The four-dimensional vector candidate inherits the scalar radial bound. -/
lemma apm_m94a03_logNormGradient_memLp_two_ball_fin_four :
    MemLp (apm_m94a03_logNormGradient :
      EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) 2
      (volume.restrict (Metric.ball 0 1)) := by
  rw [apm_m94a03_logNormGradient_memLp_iff]
  exact apm_m94a03_invNorm_memLp_two_ball_fin_four

/-- The logarithmic representative is square integrable on the
four-dimensional unit ball. -/
lemma apm_m94a03_logNorm_memLp_two_ball_fin_four :
    MemLp (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin 4) → ℝ) 2
      (volume.restrict (Metric.ball 0 1)) := by
  rw [← memLp_indicator_iff_restrict measurableSet_ball]
  let g : ℝ → ℝ := fun r ↦ if 0 < r ∧ r < 1 then Real.log r else 0
  have hfun :
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1).indicator
          apm_m94a03_logNorm = fun x => g ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [g, apm_m94a03_logNorm]
    · by_cases hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1
      · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, norm_pos_iff.mpr hx, hlt, apm_m94a03_logNorm]
      · have hnorm : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, hnorm]
  rw [hfun, apm_m94a03_memLp_radial_R4_iff]
  · have hdensity :
        (fun r : ℝ => r ^ 3 * ‖g r‖ ^ (2 : ℝ≥0∞).toReal) =
          (Set.Ioo (0 : ℝ) 1).indicator
            (fun r ↦ r ^ 3 * |Real.log r| ^ 2) := by
      funext r
      by_cases hr0 : 0 < r
      · by_cases hr1 : r < 1
        · simp [g, hr0, hr1, Real.norm_eq_abs]
        · simp [g, hr0, hr1]
      · have hrI : r ∉ Set.Ioo (0 : ℝ) 1 := fun hr ↦ hr0 hr.1
        simp [g, hr0, hrI]
    rw [hdensity]
    have hrint : Integrable
        ((Set.Ioo (0 : ℝ) 1).indicator (fun r ↦ r)) := by
      have h : IntegrableOn (fun r : ℝ ↦ r) (Set.Ioo 0 1) :=
        (continuousOn_id.integrableOn_Icc (a := (0 : ℝ)) (b := 1)).mono_set
          Ioo_subset_Icc_self
      exact h.integrable_indicator measurableSet_Ioo
    have hglobal : Integrable
        ((Set.Ioo (0 : ℝ) 1).indicator
          (fun r ↦ r ^ 3 * |Real.log r| ^ 2)) := by
      apply Integrable.mono' hrint
      · exact (((measurable_id.pow_const 3).mul
            (Real.measurable_log.abs.pow_const 2)).indicator
              measurableSet_Ioo).aestronglyMeasurable
      · filter_upwards with r
        by_cases hr : r ∈ Set.Ioo (0 : ℝ) 1
        · simp only [Set.indicator_of_mem hr, Real.norm_eq_abs,
            abs_of_pos hr.1]
          have hbound := Real.abs_log_mul_self_lt r hr.1 hr.2.le
          rw [abs_mul, abs_of_pos hr.1, mul_comm] at hbound
          have hnonneg : 0 ≤ r * |Real.log r| :=
            mul_nonneg hr.1.le (abs_nonneg _)
          rw [show r ^ 3 * |Real.log r| ^ 2 =
            r * (r * |Real.log r|) ^ 2 by ring]
          rw [abs_of_nonneg (mul_nonneg hr.1.le (sq_nonneg _))]
          have hsquare : (r * |Real.log r|) ^ 2 ≤ 1 := by nlinarith
          simpa using mul_le_mul_of_nonneg_left hsquare hr.1.le
        · simp [hr]
    exact hglobal.integrableOn
  · rw [← hfun]
    exact ((Real.measurable_log.comp measurable_norm).indicator
      measurableSet_ball).aestronglyMeasurable
  · norm_num
  · norm_num

/-- Polar `Lᵖ` reduction specialized to Euclidean two-space. -/
lemma apm_m94a03_memLp_radial_R2_iff {g : ℝ → ℝ} {p : ℝ≥0∞}
    (hg : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin 2) => g ‖x‖) volume)
    (hp0 : p ≠ 0) (hp_top : p ≠ (⊤ : ℝ≥0∞)) :
    MemLp (fun x : EuclideanSpace ℝ (Fin 2) => g ‖x‖) p volume ↔
      IntegrableOn (fun r : ℝ => r * ‖g r‖ ^ p.toReal) (Ioi 0) := by
  rw [← integrable_norm_rpow_iff hg hp0 hp_top]
  simpa only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSubDiff,
    pow_one, smul_eq_mul] using
    (MeasureTheory.integrable_fun_norm_addHaar
      (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (f := fun r : ℝ => ‖g r‖ ^ p.toReal))

/-- The inverse-radius norm is not square integrable on the two-dimensional
unit ball. -/
lemma apm_m94a03_invNorm_not_memLp_two_ball_fin_two :
    ¬ MemLp (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖⁻¹) 2
      (volume.restrict (Metric.ball 0 1)) := by
  intro h
  rw [← memLp_indicator_iff_restrict measurableSet_ball] at h
  let g : ℝ → ℝ := fun r ↦ if 0 < r ∧ r < 1 then r⁻¹ else 0
  have hfun :
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1).indicator
          (fun x => ‖x‖⁻¹) = fun x => g ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [g]
    · by_cases hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
      · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, norm_pos_iff.mpr hx, hlt]
      · have hnorm : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, hnorm]
  rw [hfun, apm_m94a03_memLp_radial_R2_iff] at h
  · have hdensity :
        (fun r : ℝ => r * ‖g r‖ ^ (2 : ℝ≥0∞).toReal) =
          (Set.Ioo (0 : ℝ) 1).indicator (fun r ↦ r⁻¹) := by
      funext r
      by_cases hr0 : 0 < r
      · by_cases hr1 : r < 1
        · simp [g, hr0, hr1, Real.norm_eq_abs, abs_of_pos hr0]
          field_simp
        · simp [g, hr0, hr1]
      · have hrI : r ∉ Set.Ioo (0 : ℝ) 1 := fun hr ↦ hr0 hr.1
        simp [g, hr0, hrI]
    rw [hdensity] at h
    have hinv : IntegrableOn (fun r : ℝ => r⁻¹) (Set.Ioo 0 1) := by
      have h' := h.mono_set
        (show Set.Ioo (0 : ℝ) 1 ⊆ Set.Ioi 0 from Set.Ioo_subset_Ioi_self)
      apply h'.congr_fun
      · intro r hr
        simp [hr]
      · exact measurableSet_Ioo
    have hrpow : IntegrableOn (fun r : ℝ => r ^ (-1 : ℝ)) (Set.Ioo 0 1) := by
      apply hinv.congr_fun
      · intro r hr
        exact (Real.rpow_neg_one r).symm
      · exact measurableSet_Ioo
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff
      (t := (1 : ℝ)) zero_lt_one).mp hrpow
    norm_num at this
  · rw [← hfun]
    exact (measurable_norm.inv.indicator measurableSet_ball).aestronglyMeasurable
  · norm_num
  · norm_num

/-- Consequently the actual classical gradient candidate cannot belong to
`L²` in dimension two. -/
lemma apm_m94a03_logNormGradient_not_memLp_two_ball_fin_two :
    ¬ MemLp (apm_m94a03_logNormGradient :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) 2
      (volume.restrict (Metric.ball 0 1)) := by
  rw [apm_m94a03_logNormGradient_memLp_iff]
  exact apm_m94a03_invNorm_not_memLp_two_ball_fin_two

/-- In contrast with the failed `L²` bound, inverse radius is integrable on
the two-dimensional unit ball. -/
lemma apm_m94a03_invNorm_memLp_one_ball_fin_two :
    MemLp (fun x : EuclideanSpace ℝ (Fin 2) => ‖x‖⁻¹) 1
      (volume.restrict (Metric.ball 0 1)) := by
  rw [← memLp_indicator_iff_restrict measurableSet_ball]
  let g : ℝ → ℝ := fun r ↦ if 0 < r ∧ r < 1 then r⁻¹ else 0
  have hfun :
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1).indicator
          (fun x => ‖x‖⁻¹) = fun x => g ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [g]
    · by_cases hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
      · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, norm_pos_iff.mpr hx, hlt]
      · have hnorm : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, hnorm]
  rw [hfun, apm_m94a03_memLp_radial_R2_iff]
  · have hdensity :
        (fun r : ℝ => r * ‖g r‖ ^ (1 : ℝ≥0∞).toReal) =
          (Set.Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) := by
      funext r
      by_cases hr0 : 0 < r
      · by_cases hr1 : r < 1
        · simp [g, hr0, hr1, Real.norm_eq_abs, abs_of_pos hr0]
          field_simp
        · simp [g, hr0, hr1]
      · have hrI : r ∉ Set.Ioo (0 : ℝ) 1 := fun hr ↦ hr0 hr.1
        simp [g, hr0, hrI]
    rw [hdensity]
    exact ((integrableOn_const (s := Set.Ioo (0 : ℝ) 1)
      (measure_Ioo_lt_top.ne)).integrable_indicator
      measurableSet_Ioo).integrableOn
  · rw [← hfun]
    exact (measurable_norm.inv.indicator measurableSet_ball).aestronglyMeasurable
  · norm_num
  · norm_num

/-- Hence the classical vector candidate has the local `L¹` regularity needed
by distributional uniqueness in dimension two. -/
lemma apm_m94a03_logNormGradient_memLp_one_ball_fin_two :
    MemLp (apm_m94a03_logNormGradient :
      EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) 1
      (volume.restrict (Metric.ball 0 1)) := by
  rw [apm_m94a03_logNormGradient_memLp_iff]
  exact apm_m94a03_invNorm_memLp_one_ball_fin_two

def apm_m94a03_IsWeakGradientOn {n : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ (i : Fin n) (φ : EuclideanSpace ℝ (Fin n) → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ → Function.support φ ⊆ s →
      ∫ x, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)
          ∂(volume.restrict s) =
        -∫ x, (g x i) * φ x ∂(volume.restrict s)

def apm_m94a03_InH1UnitBall (n : ℕ) : Prop :=
  let E := EuclideanSpace ℝ (Fin n)
  let Ω : Set E := Metric.ball 0 1
  MemLp (apm_m94a03_logNorm : E → ℝ) 2 (volume.restrict Ω) ∧
  ∃ g : E → E, MemLp g 2 (volume.restrict Ω) ∧
    apm_m94a03_IsWeakGradientOn Ω apm_m94a03_logNorm g

/-- Coordinatewise uniqueness of weak gradients on an open set, at the local
integrability interface required by the distributional fundamental lemma. -/
lemma apm_m94a03_weakGradient_coordinate_ae_eq {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : IsOpen s)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hg : apm_m94a03_IsWeakGradientOn s f g)
    (hk : apm_m94a03_IsWeakGradientOn s f k)
    (i : Fin n) (hgloc : LocallyIntegrable (fun x ↦ g x i) volume)
    (hkloc : LocallyIntegrable (fun x ↦ k x i) volume) :
    ∀ᵐ x ∂volume, x ∈ s → g x i = k x i := by
  have hzero : ∀ᵐ x ∂volume, x ∈ s → (g x i - k x i) = 0 :=
    hs.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hgloc.sub hkloc).locallyIntegrableOn s) (by
      intro q hqdiff hqcompact hqtsupport
      have hqsupport : Function.support q ⊆ s :=
        (subset_tsupport q).trans hqtsupport
      have eg := hg i q hqdiff hqcompact hqsupport
      have ek := hk i q hqdiff hqcompact hqsupport
      have heq :
          ∫ x, (g x i) * q x ∂(volume.restrict s) =
            ∫ x, (k x i) * q x ∂(volume.restrict s) := by
        linarith
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := s) (fun x hx ↦ by
          have hqx : q x = 0 := by
            rw [← Function.notMem_support]
            exact fun hmem ↦ hx (hqsupport hmem)
          simp [hqx])]
      simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
      rw [integral_sub]
      · simpa [mul_comm] using sub_eq_zero.mpr heq
      · exact (hgloc.integrable_smul_left_of_hasCompactSupport
          hqdiff.continuous hqcompact).restrict
      · exact (hkloc.integrable_smul_left_of_hasCompactSupport
          hqdiff.continuous hqcompact).restrict)
  filter_upwards [hzero] with x hx hxs
  exact sub_eq_zero.mp (hx hxs)

/-- Replacing a weak gradient by its indicator on the domain does not change
the restricted weak-gradient identity. -/
lemma apm_m94a03_IsWeakGradientOn.indicator {n : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hg : apm_m94a03_IsWeakGradientOn s f g) :
    apm_m94a03_IsWeakGradientOn s f (s.indicator g) := by
  intro i φ hφdiff hφcompact hφsupport
  rw [hg i φ hφdiff hφcompact hφsupport]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  simp [Set.indicator_of_mem hx]

/-- A coordinate of a disk-`L²` vector field, extended by zero, is globally
locally integrable. -/
lemma apm_m94a03_indicator_coordinate_locallyIntegrable_fin_two {p : ℝ≥0∞}
    {g : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hp : 1 ≤ p) (hg : MemLp g p
      (volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1))) (i : Fin 2) :
    LocallyIntegrable (fun x ↦
      ((Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1).indicator g x) i)
      volume := by
  letI : IsFiniteMeasure
      (volume.restrict (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    IsFiniteMeasure.mk (by
      simpa using (measure_ball_lt_top (μ :=
        (volume : Measure (EuclideanSpace ℝ (Fin 2))))
        (x := (0 : EuclideanSpace ℝ (Fin 2))) (r := (1 : ℝ))))
  have hi : MemLp (fun x ↦ g x i) p
      (volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) := by
    apply hg.of_le
    · exact (EuclideanSpace.proj i).continuous.comp_aestronglyMeasurable
        hg.aestronglyMeasurable
    · filter_upwards with x
      exact PiLp.norm_apply_le (g x) i
  have hi' : Integrable (fun x ↦ g x i)
      (volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)) :=
    hi.integrable hp
  have hloc := ((integrable_indicator_iff measurableSet_ball).2 hi').locallyIntegrable
  apply hloc.congr
  filter_upwards with x
  by_cases hx : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
  · simp [Set.indicator, hx]
  · simp [Set.indicator, hx]

/-- Why this unblocks the three-dimensional positive conjunct of
`apm_m94a03`: this is the missing radial logarithm-square integrability
statement. Together with the already proved gradient `L²` bound, it supplies
the function-membership half of `apm_m94a03_InH1UnitBall 3`. -/
theorem apm_m94A03_bridge_logNorm_memLp_two_ball_fin_three :
    MemLp (apm_m94a03_logNorm :
      EuclideanSpace ℝ (Fin 3) → ℝ) 2
      (volume.restrict
        (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) := by
  rw [← memLp_indicator_iff_restrict measurableSet_ball]
  let g : ℝ → ℝ := fun r ↦ if 0 < r ∧ r < 1 then Real.log r else 0
  have hfun :
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1).indicator
          apm_m94a03_logNorm = fun x => g ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [g, apm_m94a03_logNorm]
    · by_cases hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1
      · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [Set.indicator_apply, hball, g, norm_pos_iff.mpr hx, hlt,
          apm_m94a03_logNorm]
      · have hnorm : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [Set.indicator_apply, hball, g, hnorm, apm_m94a03_logNorm]
  rw [hfun, ConstructionTargets.RadialIntegrationR3.memLp_radial_R3_iff]
  · have hdensity :
        (fun r : ℝ => r ^ 2 * ‖g r‖ ^ (2 : ℝ≥0∞).toReal) =
          (Set.Ioo (0 : ℝ) 1).indicator
            (fun r ↦ r ^ 2 * |Real.log r| ^ 2) := by
      funext r
      by_cases hr0 : 0 < r
      · by_cases hr1 : r < 1
        · simp [g, hr0, hr1, Real.norm_eq_abs]
        · simp [g, hr0, hr1]
      · have hrI : r ∉ Set.Ioo (0 : ℝ) 1 := fun hr ↦ hr0 hr.1
        simp [g, hr0, hrI]
    rw [hdensity]
    have hone : Integrable
        ((Set.Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ))) :=
      (integrableOn_const (s := Set.Ioo (0 : ℝ) 1)
        (measure_Ioo_lt_top.ne)).integrable_indicator measurableSet_Ioo
    have hglobal : Integrable
        ((Set.Ioo (0 : ℝ) 1).indicator
          (fun r ↦ r ^ 2 * |Real.log r| ^ 2)) := by
      apply Integrable.mono' hone
      · exact (((measurable_id.pow_const 2).mul
            (Real.measurable_log.abs.pow_const 2)).indicator
              measurableSet_Ioo).aestronglyMeasurable
      · filter_upwards with r
        by_cases hr : r ∈ Set.Ioo (0 : ℝ) 1
        · simp only [Set.indicator_of_mem hr, Real.norm_eq_abs, abs_one]
          have hbound := Real.abs_log_mul_self_lt r hr.1 hr.2.le
          rw [abs_mul, abs_of_pos hr.1, mul_comm] at hbound
          have hnonneg : 0 ≤ r * |Real.log r| :=
            mul_nonneg hr.1.le (abs_nonneg _)
          rw [← mul_pow, abs_of_nonneg (sq_nonneg _)]
          nlinarith [sq_nonneg (r * |Real.log r|)]
        · simp [hr]
    exact hglobal.integrableOn
  · rw [← hfun]
    exact ((Real.measurable_log.comp measurable_norm).indicator
      measurableSet_ball).aestronglyMeasurable
  · norm_num
  · norm_num

/-- The logarithm itself is integrable on the planar unit disk.  This is the
minimal membership needed to pass the regularized integration-by-parts
identity to the limit in the negative case. -/
lemma apm_m94a03_logNorm_memLp_one_ball_fin_two :
    MemLp (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin 2) → ℝ) 1
      (volume.restrict (Metric.ball 0 1)) := by
  rw [← memLp_indicator_iff_restrict measurableSet_ball]
  let g : ℝ → ℝ := fun r ↦ if 0 < r ∧ r < 1 then Real.log r else 0
  have hfun :
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1).indicator
          apm_m94a03_logNorm = fun x => g ‖x‖ := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [g, apm_m94a03_logNorm]
    · by_cases hball : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1
      · have hlt : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, norm_pos_iff.mpr hx, hlt, apm_m94a03_logNorm]
      · have hnorm : ¬ ‖x‖ < 1 := by simpa [Metric.mem_ball] using hball
        simp [hball, g, hnorm]
  rw [hfun, apm_m94a03_memLp_radial_R2_iff]
  · have hdensity :
        (fun r : ℝ => r * ‖g r‖ ^ (1 : ℝ≥0∞).toReal) =
          (Set.Ioo (0 : ℝ) 1).indicator (fun r ↦ r * |Real.log r|) := by
      funext r
      by_cases hr0 : 0 < r
      · by_cases hr1 : r < 1
        · simp [g, hr0, hr1, Real.norm_eq_abs]
        · simp [g, hr0, hr1]
      · have hrI : r ∉ Set.Ioo (0 : ℝ) 1 := fun hr ↦ hr0 hr.1
        simp [g, hr0, hrI]
    rw [hdensity]
    have hone : Integrable
        ((Set.Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ))) :=
      (integrableOn_const (s := Set.Ioo (0 : ℝ) 1)
        (measure_Ioo_lt_top.ne)).integrable_indicator measurableSet_Ioo
    have hglobal : Integrable
        ((Set.Ioo (0 : ℝ) 1).indicator
          (fun r ↦ r * |Real.log r|)) := by
      apply Integrable.mono' hone
      · exact ((measurable_id.mul Real.measurable_log.abs).indicator
          measurableSet_Ioo).aestronglyMeasurable
      · filter_upwards with r
        by_cases hr : r ∈ Set.Ioo (0 : ℝ) 1
        · simp only [Set.indicator_of_mem hr, Real.norm_eq_abs, abs_one]
          have hbound := Real.abs_log_mul_self_lt r hr.1 hr.2.le
          rw [abs_mul, abs_of_pos hr.1, mul_comm] at hbound
          rw [abs_of_nonneg (mul_nonneg hr.1.le (abs_nonneg _))]
          exact hbound.le
        · simp [hr]
    exact hglobal.integrableOn
  · rw [← hfun]
    exact ((Real.measurable_log.comp measurable_norm).indicator
      measurableSet_ball).aestronglyMeasurable
  · norm_num
  · norm_num

/-- Why this unblocks the three-dimensional positive conjunct of
`apm_m94a03`: this is the punctured-ball integration-by-parts theorem,
including disappearance of the inner spherical boundary term. It identifies
the compiled `L²` vector field with the distributional gradient required by
the frozen predicate. -/
lemma apm_m94a03_logNormGradient_weak_of_memLp {n : ℕ} (hn : 0 < n)
    (hlog : MemLp (apm_m94a03_logNorm :
      EuclideanSpace ℝ (Fin n) → ℝ) 1
      (volume.restrict (Metric.ball 0 1)))
    (hinv : MemLp (fun x : EuclideanSpace ℝ (Fin n) ↦ ‖x‖⁻¹) 1
      (volume.restrict (Metric.ball 0 1))) :
    apm_m94a03_IsWeakGradientOn
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin n) → ℝ)
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  intro i φ hφ hφc hφsupport
  let Ω : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    fderiv ℝ φ x (EuclideanSpace.single i 1)
  have hφzero : ∀ x, x ∉ Ω → φ x = 0 := by
    intro x hx
    rw [← Function.notMem_support]
    exact fun h ↦ hx (hφsupport h)
  have hqzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∉ Ω → q x = 0 := by
    have hsphere : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        x ∉ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp only [ae_iff, Classical.not_not]
      exact Measure.addHaar_sphere volume 0 1
    filter_upwards [hsphere] with x hxs hxΩ
    have hxclosed : x ∉ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le]
      have hnlt : ¬ ‖x‖ < 1 := by simpa [Ω, Metric.mem_ball] using hxΩ
      have hne : ‖x‖ ≠ 1 := by
        simpa [Metric.mem_sphere, dist_zero_right, eq_comm] using hxs
      exact lt_of_le_of_ne (le_of_not_gt hnlt) hne.symm
    have hevent : ∀ᶠ y in nhds x, y ∉ Ω := by
      apply (Metric.isClosed_closedBall.isOpen_compl.eventually_mem hxclosed).mono
      intro y hy hyΩ
      exact hy (Metric.ball_subset_closedBall hyΩ)
    have heq : φ =ᶠ[nhds x] (fun _ ↦ (0 : ℝ)) := by
      filter_upwards [hevent] with y hy
      exact hφzero y hy
    change fderiv ℝ φ x (EuclideanSpace.single i 1) = 0
    rw [heq.fderiv_eq]
    simp
  have hrestrict (F : EuclideanSpace ℝ (Fin n) → ℝ)
      (hF : ∀ᵐ x ∂volume, x ∉ Ω → F x = 0) :
      ∫ x, F x ∂(volume.restrict Ω) = ∫ x, F x := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [hF] with x hx
    by_cases hxo : x ∈ Ω
    · change Ω.indicator F x = F x
      rw [Set.indicator_of_mem hxo]
    · change Ω.indicator F x = F x
      rw [Set.indicator_of_notMem hxo, hx hxo]
  have hleft (k : ℕ) :
      ∫ x, apm_m94a03_logNormRegularized (1 / ((k : ℝ) + 1)) x * q x
          ∂(volume.restrict Ω) =
        ∫ x, apm_m94a03_logNormRegularized (1 / ((k : ℝ) + 1)) x * q x := by
    apply hrestrict
    filter_upwards [hqzero] with x hx hxo
    simp [hx hxo]
  have hright (k : ℕ) :
      ∫ x, ((‖x‖ ^ 2 + 1 / ((k : ℝ) + 1))⁻¹ * x i) * φ x
          ∂(volume.restrict Ω) =
        ∫ x, ((‖x‖ ^ 2 + 1 / ((k : ℝ) + 1))⁻¹ * x i) * φ x := by
    apply hrestrict
    filter_upwards with x hxo
    simp [hφzero x hxo]
  have hk (k : ℕ) :
      ∫ x, apm_m94a03_logNormRegularized (1 / ((k : ℝ) + 1)) x * q x
          ∂(volume.restrict Ω) =
        -∫ x, ((‖x‖ ^ 2 + 1 / ((k : ℝ) + 1))⁻¹ * x i) * φ x
          ∂(volume.restrict Ω) := by
    rw [hleft, hright]
    exact apm_m94a03_integral_logNormRegularized_mul_fderiv
      (apm_m94a03_regularizationScale_pos k) i φ hφ hφc
  have hloglim := apm_m94a03_integral_logNormRegularized_tendsto
    hn hlog i φ hφ hφc
  letI : IsFiniteMeasure (volume.restrict Ω) := IsFiniteMeasure.mk (by
    simpa [Ω] using (measure_ball_lt_top (μ :=
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (x := (0 : EuclideanSpace ℝ (Fin n))) (r := (1 : ℝ))))
  have hgradlim := apm_m94a03_integral_regularizedGradient_tendsto
    hn Ω measurableSet_ball (hinv.integrable (by norm_num))
    i φ hφ hφc
  exact tendsto_nhds_unique hloglim
    ((hgradlim.neg.congr' (Filter.Eventually.of_forall fun k ↦ by rw [hk k])).trans
      tendsto_id)

theorem apm_m94A03_bridge_logNormGradient_weak_fin_three :
    apm_m94a03_IsWeakGradientOn
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin 3) → ℝ)
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) := by
  letI : IsFiniteMeasure (volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
    IsFiniteMeasure.mk (by simpa using (measure_ball_lt_top (μ :=
      (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := (1 : ℝ))))
  apply apm_m94a03_logNormGradient_weak_of_memLp (by norm_num)
    (apm_m94A03_bridge_logNorm_memLp_two_ball_fin_three.mono_exponent
      (by norm_num))
  exact apm_m94a03_invNorm_memLp_two_ball_fin_three.mono_exponent (by norm_num)

lemma apm_m94a03_logNormGradient_weak_fin_two :
    apm_m94a03_IsWeakGradientOn
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin 2) → ℝ)
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
  exact apm_m94a03_logNormGradient_weak_of_memLp (by norm_num)
    apm_m94a03_logNorm_memLp_one_ball_fin_two
    apm_m94a03_invNorm_memLp_one_ball_fin_two

lemma apm_m94a03_logNormGradient_weak_fin_four :
    apm_m94a03_IsWeakGradientOn
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin 4) → ℝ)
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4)) := by
  letI : IsFiniteMeasure (volume.restrict
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1)) :=
    IsFiniteMeasure.mk (by simpa using (measure_ball_lt_top (μ :=
      (volume : Measure (EuclideanSpace ℝ (Fin 4))))
      (x := (0 : EuclideanSpace ℝ (Fin 4))) (r := (1 : ℝ))))
  apply apm_m94a03_logNormGradient_weak_of_memLp (by norm_num)
    (apm_m94a03_logNorm_memLp_two_ball_fin_four.mono_exponent (by norm_num))
  exact apm_m94a03_invNorm_memLp_two_ball_fin_four.mono_exponent (by norm_num)

/-- All analytic membership bookkeeping for the three-dimensional positive
conjunct is discharged once the weak identity is supplied. -/
lemma apm_m94a03_inH1_fin_three : apm_m94a03_InH1UnitBall 3 := by
  refine ⟨apm_m94A03_bridge_logNorm_memLp_two_ball_fin_three,
    apm_m94a03_logNormGradient, ?_, ?_⟩
  · exact apm_m94a03_logNormGradient_memLp_two_ball_fin_three
  · exact apm_m94A03_bridge_logNormGradient_weak_fin_three

/-- The analogous dimension-four assembly has only the weak-gradient identity
as an input; both `L²` obligations are already proved above. -/
lemma apm_m94a03_inH1_fin_four_of_weak
    (hweak : apm_m94a03_IsWeakGradientOn
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin 4) → ℝ)
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin 4) → EuclideanSpace ℝ (Fin 4))) :
    apm_m94a03_InH1UnitBall 4 := by
  refine ⟨apm_m94a03_logNorm_memLp_two_ball_fin_four,
    apm_m94a03_logNormGradient, ?_, hweak⟩
  exact apm_m94a03_logNormGradient_memLp_two_ball_fin_four

/-- Once the classical candidate's weak identity is known, uniqueness and its
failed `L²` bound rule out the two-dimensional Sobolev membership. -/
lemma apm_m94a03_not_inH1_fin_two_of_weak
    (hcandidate : apm_m94a03_IsWeakGradientOn
      (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (apm_m94a03_logNorm : EuclideanSpace ℝ (Fin 2) → ℝ)
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))) :
    ¬ apm_m94a03_InH1UnitBall 2 := by
  rintro ⟨_, g, hgLp, hgweak⟩
  let Ω : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball 0 1
  have hgind := hgweak.indicator (measurableSet_ball : MeasurableSet Ω)
  have hcind := hcandidate.indicator (measurableSet_ball : MeasurableSet Ω)
  have hcoord (i : Fin 2) :
      ∀ᵐ x ∂volume, x ∈ Ω →
        (Ω.indicator g x) i =
          (Ω.indicator apm_m94a03_logNormGradient x) i :=
    apm_m94a03_weakGradient_coordinate_ae_eq Metric.isOpen_ball hgind hcind i
      (apm_m94a03_indicator_coordinate_locallyIntegrable_fin_two
        (p := 2) (by norm_num) hgLp i)
      (apm_m94a03_indicator_coordinate_locallyIntegrable_fin_two
        (p := 1) (by norm_num)
          apm_m94a03_logNormGradient_memLp_one_ball_fin_two i)
  have hvec : g =ᵐ[volume.restrict Ω]
      (apm_m94a03_logNormGradient :
        EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
    filter_upwards [ae_restrict_of_ae (hcoord 0),
      ae_restrict_of_ae (hcoord 1), ae_restrict_mem measurableSet_ball]
      with x h0 h1 hx
    apply PiLp.ext
    intro i
    fin_cases i
    · simpa [Ω, Set.indicator_of_mem hx] using h0 hx
    · simpa [Ω, Set.indicator_of_mem hx] using h1 hx
  apply apm_m94a03_logNormGradient_not_memLp_two_ball_fin_two
  apply hgLp.congr_norm apm_m94a03_logNormGradient_aestronglyMeasurable
  filter_upwards [hvec] with x hx
  rw [hx]

theorem apm_m94a03 :
    ¬ apm_m94a03_InH1UnitBall 2 ∧
    apm_m94a03_InH1UnitBall 3 ∧
    apm_m94a03_InH1UnitBall 4 := by
  /-
  CLOSER HOP 1 (partial). The classical candidate gradient is now defined by
  `apm_m94a03_logNormGradient`, and
  `apm_m94a03_norm_logNormGradient` proves its exact norm is `‖x‖⁻¹` away
  from zero. Thus its squared radial singularity is pinned for both the
  positive and negative dimension thresholds.

  The remaining boundary: the positive cases require proving radial `L²` integrability of
  `log ‖x‖` and of the candidate gradient `x / ‖x‖ ^ 2` in dimensions three
  and four, then establishing the custom weak-gradient identity by integrating
  over a punctured ball and showing the inner-sphere boundary term tends to
  zero. The negative two-dimensional case additionally requires uniqueness of
  distributional weak gradients, so that any hypothetical `L²` gradient is
  identified almost everywhere with the non-square-integrable classical
  gradient away from zero.

  Renewed searches of Mathlib and the repository for radial/polar integration and weak
  derivative infrastructure. The repository has a specialized three-
  dimensional radial integral construction in `a95A03`, but no general
  dimension-two/four formula or compiled route for this custom Euclidean-space
  weak-gradient predicate. I did not complete the punctured-domain divergence
  theorem, boundary-limit, and weak-gradient uniqueness machinery required by
  all three conjuncts within this pass. `Complex.integral_comp_polarCoord_symm`
  covers dimension two after an isometric transport, but no corresponding
  ready-made general Euclidean radial formula or weak-gradient uniqueness
  theorem was found in `LEMMA-INDEX.md`, `ConstructionTargets/`, solved
  siblings, or git history.

  Closer hop 2 removes the measurability and vector-to-scalar interfaces from
  the remaining radial problem. `apm_m94a03_norm_logNormGradient_all` extends
  the norm identity through the totalized origin. The two measurable helpers
  prove strong measurability for arbitrary ambient measures, and
  `apm_m94a03_logNormGradient_memLp_iff` uses `memLp_congr_norm` to show that
  the vector candidate belongs to any `Lᵖ(μ)` exactly when the scalar function
  `x ↦ ‖x‖⁻¹` does. Thus no a.e.-exception or coordinatewise measurability
  bookkeeping remains in the dimension threshold.

  Further searches covered Mathlib's norm-derivative, Euclidean inner-product,
  `MemLp`, Hausdorff/radial, and divergence-theorem APIs, plus the radial
  artifacts `a95A03` and `m95J02`. They provide local derivative and
  specialized radial ingredients but still no dimension-parametric formula
  for the restricted unit ball. The remaining bridges are now the scalar
  radial integrals, punctured-ball integration by parts, and weak-gradient
  uniqueness in dimension two. The frozen statement is unchanged.

  CLOSER HOP 3 (partial). The dimension-three gradient-integrability bridge
  is now closed using the previously proved reusable module
  `ConstructionTargets.RadialIntegrationR3`.
  `apm_m94a03_invNorm_memLp_two_ball_fin_three` converts restriction to an
  indicator, rewrites it as a radial profile, and applies
  `memLp_radial_R3_iff`; its density is exactly the indicator of `(0,1)`.
  `apm_m94a03_logNormGradient_memLp_two_ball_fin_three` transfers this scalar
  result to the vector candidate via the hop-2 norm equivalence.

  The three-dimensional positive conjunct still needs logarithm `L²`
  integrability and the punctured-ball weak-gradient identity. Dimension four
  lacks a corresponding compiled radial specialization, while dimension two
  still needs weak-gradient uniqueness and inverse-radius nonintegrability.
  The general `integral_fun_norm_addHaar` interface is a possible route, but
  the distributional integration-by-parts bridge remains substantial. The
  frozen statement is unchanged.
  -/
  exact ⟨apm_m94a03_not_inH1_fin_two_of_weak
      apm_m94a03_logNormGradient_weak_fin_two,
    apm_m94a03_inH1_fin_three,
    apm_m94a03_inH1_fin_four_of_weak
      apm_m94a03_logNormGradient_weak_fin_four⟩
