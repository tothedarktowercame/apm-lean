import Mathlib

/-!
# APM a98A07

## Statement repairs

None.

## Encoding questions

None.  “Uniformly on compact subsets” is represented by Mathlib's
`TendstoLocallyUniformlyOn` predicate.
-/

open Filter MeasureTheory Metric Set
open scoped Topology

/-- The real boundary majorant from the frozen hypothesis. -/
noncomputable def apm_a98A07_majorant (t : ℝ) : ℝ :=
  1 / (t * (Real.log (t / (4 * Real.pi))) ^ 2)

/-- The logarithm in the boundary majorant stays strictly negative throughout
the circle parameter interval. -/
lemma apm_a98A07_log_ratio_neg {t : ℝ}
    (ht : 0 < t) (htop : t < 2 * Real.pi) :
    Real.log (t / (4 * Real.pi)) < 0 := by
  apply Real.log_neg
  · positivity
  · apply (div_lt_one (by positivity : 0 < 4 * Real.pi)).2
    nlinarith [Real.pi_pos]

/-- The majorant is strictly positive throughout the boundary parameter
interval. -/
lemma apm_a98A07_majorant_pos {t : ℝ}
    (ht : 0 < t) (htop : t < 2 * Real.pi) :
    0 < apm_a98A07_majorant t := by
  rw [apm_a98A07_majorant]
  apply one_div_pos.mpr
  exact mul_pos ht (sq_pos_of_neg (apm_a98A07_log_ratio_neg ht htop))

/-- The boundary majorant is measurable, so once its logarithmic improper
integral is established it can be used directly by dominated convergence. -/
lemma apm_a98A07_majorant_measurable :
    Measurable apm_a98A07_majorant := by
  unfold apm_a98A07_majorant
  fun_prop

/-- The logarithmic tail which appears after the reciprocal change of
variables is integrable. -/
lemma apm_a98A07_integrable_log_tail :
    IntegrableOn (fun x : ℝ => 1 / (x * (Real.log x) ^ 2)) (Ioi 2) := by
  have hderiv : ∀ x ∈ Ici (2 : ℝ),
      HasDerivAt (fun y : ℝ => -(Real.log y)⁻¹)
        (1 / (x * (Real.log x) ^ 2)) x := by
    intro x hx
    have hx' : (2 : ℝ) ≤ x := hx
    have hxpos : 0 < x := by linarith
    have hxlog : Real.log x ≠ 0 := by
      exact Real.log_ne_zero_of_pos_of_ne_one hxpos (by linarith)
    convert (Real.hasDerivAt_log hxpos.ne').inv hxlog |>.neg using 1 <;> field_simp
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' (l := 0) hderiv ?_ ?_
  · intro x hx
    have hxpos : 0 < x := lt_trans (by norm_num) hx
    exact one_div_nonneg.mpr (mul_nonneg hxpos.le (sq_nonneg _))
  · have hinv : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop
    simpa using hinv.neg

/-- The boundary majorant is integrable on the circle parameter interval. -/
lemma apm_a98A07_majorant_integrable :
    Integrable apm_a98A07_majorant
      ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))) := by
  change IntegrableOn apm_a98A07_majorant (Ioo 0 (2 * Real.pi))
  let c : ℝ := 4 * Real.pi
  let φ : ℝ → ℝ := fun x => c / x
  have hc : 0 < c := by dsimp [c]; positivity
  have himage : φ '' Ioi (2 : ℝ) = Ioo 0 (2 * Real.pi) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxpos : 0 < x := lt_trans (by norm_num) hx
      constructor
      · exact div_pos hc hxpos
      · dsimp [φ, c]
        rw [div_lt_iff₀ hxpos]
        nlinarith [mul_lt_mul_of_pos_right hx Real.pi_pos]
    · intro hy
      refine ⟨c / y, ?_, ?_⟩
      · have hypos : 0 < y := hy.1
        rw [mem_Ioi, lt_div_iff₀ hypos]
        dsimp [c]
        nlinarith [Real.pi_pos, hy.2]
      · dsimp [φ]
        field_simp
  have hderiv : ∀ x ∈ Ioi (2 : ℝ),
      HasDerivWithinAt φ (-c / x ^ 2) (Ioi 2) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
    convert ((hasDerivAt_const x c).div (hasDerivAt_id x) hx0).hasDerivWithinAt using 1 <;>
      simp [φ]
  have hinj : InjOn φ (Ioi (2 : ℝ)) := by
    intro x hx y hy hxy
    dsimp [φ] at hxy
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans (by norm_num) hx)
    have hy0 : y ≠ 0 := ne_of_gt (lt_trans (by norm_num) hy)
    field_simp [hx0, hy0] at hxy
    exact hxy.symm
  rw [← himage]
  rw [MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi hderiv hinj]
  apply apm_a98A07_integrable_log_tail.congr_fun
  intro x hx
  have hxpos : 0 < x := lt_trans (by norm_num) hx
  have hx0 : x ≠ 0 := hxpos.ne'
  have hlog : Real.log (x⁻¹) = -Real.log x := by
    rw [Real.log_inv]
  have hquot : 4 * Real.pi / x / (4 * Real.pi) = x⁻¹ := by
    field_simp [hx0, Real.pi_ne_zero]
  have habs : |-(4 * Real.pi) / x ^ 2| = 4 * Real.pi / x ^ 2 := by
    have hn : -(4 * Real.pi) < 0 := neg_neg_of_pos (by positivity)
    rw [abs_of_neg (div_neg_of_neg_of_pos hn (sq_pos_of_pos hxpos))]
    ring_nf
  simp only [smul_eq_mul, apm_a98A07_majorant, φ, c]
  rw [habs, hquot, hlog]
  field_simp
  ring
  all_goals exact measurableSet_Ioi

/-- A canonical pointwise limit, with zero off the set where a limit exists. -/
noncomputable def apm_a98A07_aeLimit (F : ℕ → ℝ → ℂ) (t : ℝ) : ℂ :=
  by
    classical
    exact if h : ∃ w : ℂ, Tendsto (fun n => F n t) atTop (𝓝 w) then Classical.choose h else 0

lemma apm_a98A07_tendsto_aeLimit {F : ℕ → ℝ → ℂ} {t : ℝ}
    (h : ∃ w : ℂ, Tendsto (fun n => F n t) atTop (𝓝 w)) :
    Tendsto (fun n => F n t) atTop (𝓝 (apm_a98A07_aeLimit F t)) := by
  classical
  simp only [apm_a98A07_aeLimit, dif_pos h]
  exact Classical.choose_spec h

/-- Dominated pointwise convergence of boundary traces gives convergence in
`L¹`.  This packages the measurable selection needed by the main proof. -/
lemma apm_a98A07_tendsto_integral_norm_sub
    {F : ℕ → ℝ → ℂ} {M : ℝ → ℝ} {mu : Measure ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) mu)
    (hM : Integrable M mu)
    (hbound : ∀ n, ∀ᵐ t ∂mu, ‖F n t‖ ≤ M t)
    (hconv : ∀ᵐ t ∂mu, ∃ w : ℂ, Tendsto (fun n => F n t) atTop (𝓝 w)) :
    Tendsto (fun n => ∫ t, ‖F n t - apm_a98A07_aeLimit F t‖ ∂mu) atTop (𝓝 0) := by
  have hlim : ∀ᵐ t ∂mu,
      Tendsto (fun n => F n t) atTop (𝓝 (apm_a98A07_aeLimit F t)) :=
    hconv.mono fun _ ht => apm_a98A07_tendsto_aeLimit ht
  have hmeas : AEStronglyMeasurable (apm_a98A07_aeLimit F) mu :=
    aestronglyMeasurable_of_tendsto_ae atTop hF hlim
  have hlimBound : ∀ᵐ t ∂mu, ‖apm_a98A07_aeLimit F t‖ ≤ M t := by
    filter_upwards [hlim, eventually_countable_forall.2 hbound] with t ht hb
    exact le_of_tendsto' ht.norm fun n => hb n
  have hdom : ∀ n, ∀ᵐ t ∂mu,
      ‖‖F n t - apm_a98A07_aeLimit F t‖‖ ≤ 2 * M t := by
    intro n
    filter_upwards [hbound n, hlimBound] with t hn hl
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖F n t - apm_a98A07_aeLimit F t‖ ≤ ‖F n t‖ + ‖apm_a98A07_aeLimit F t‖ := norm_sub_le _ _
      _ ≤ M t + M t := add_le_add hn hl
      _ = 2 * M t := by ring
  have hpoint : ∀ᵐ t ∂mu,
      Tendsto (fun n => ‖F n t - apm_a98A07_aeLimit F t‖) atTop (𝓝 0) :=
    hlim.mono fun t ht => by
      have hc : Tendsto (fun _ : ℕ => apm_a98A07_aeLimit F t) atTop
          (𝓝 (apm_a98A07_aeLimit F t)) := tendsto_const_nhds
      simpa using (ht.sub hc).norm
  simpa using MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun t => 2 * M t) (fun n => (hF n).sub hmeas |>.norm) (hM.const_mul 2)
      hdom hpoint

/-- Uniform Cauchy-kernel estimate on a closed subdisk. -/
lemma apm_a98A07_cauchy_kernel_bound {r : ℝ} (hr : r < 1) {z a : ℂ}
    (hz : ‖z‖ ≤ r) (t : ℝ) :
    ‖(Complex.exp (Complex.I * (t : ℂ)) - z)⁻¹ *
        (Complex.exp (Complex.I * (t : ℂ)) * a)‖ ≤ (1 - r)⁻¹ * ‖a‖ := by
  let w := Complex.exp (Complex.I * (t : ℂ))
  have hw : ‖w‖ = 1 := by simp [w, Complex.norm_exp]
  have hdist : 1 - r ≤ ‖w - z‖ := by
    calc
      1 - r ≤ ‖w‖ - ‖z‖ := by rw [hw]; linarith
      _ ≤ ‖w - z‖ := norm_sub_norm_le w z
  have hpos : 0 < 1 - r := sub_pos.mpr hr
  have hdistpos : 0 < ‖w - z‖ := hpos.trans_le hdist
  have hinv : ‖w - z‖⁻¹ ≤ (1 - r)⁻¹ := by
    exact (inv_le_inv₀ hdistpos hpos).2 hdist
  simp only [norm_mul, norm_inv, w, hw, one_mul]
  exact mul_le_mul_of_nonneg_right hinv (norm_nonneg a)

/-- Boundary traces of functions continuous on the closed disk are strongly
measurable for the restricted parameter measure. -/
lemma apm_a98A07_trace_aestronglyMeasurable {f : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall 0 1)) :
    AEStronglyMeasurable
      (fun t : ℝ => f (Complex.exp (Complex.I * (t : ℂ))))
      ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))) := by
  have hg : Continuous (fun t : ℝ => Complex.exp (Complex.I * (t : ℂ))) := by fun_prop
  have hmem : ∀ t : ℝ, Complex.exp (Complex.I * (t : ℂ)) ∈ closedBall (0 : ℂ) 1 := by
    intro t
    simp [mem_closedBall, Complex.norm_exp]
  have hc := hf.comp_continuous hg hmem
  exact (by simpa [Function.comp_def] using hc.aestronglyMeasurable.restrict)

/-- Rewrite the unit-circle integral using the boundary parametrization from
the frozen statement and an open-interval set integral. -/
lemma apm_a98A07_circleIntegral_eq_parameterIntegral (q : ℂ → ℂ) :
    (∮ z in C(0, 1), q z) =
      ∫ t in Ioo (0 : ℝ) (2 * Real.pi),
        (Complex.exp (Complex.I * (t : ℂ)) * Complex.I) *
          q (Complex.exp (Complex.I * (t : ℂ))) := by
  rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
  apply integral_congr_ae
  filter_upwards with t
  simp only [deriv_circleMap, circleMap_zero, smul_eq_mul]
  norm_num
  congr 2 <;> ring

/-- Cauchy's formula in the exact real-parameter form consumed by the boundary
`L¹` estimate. -/
lemma apm_a98A07_cauchy_parameter_formula {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∫ t in Ioo (0 : ℝ) (2 * Real.pi),
        (Complex.exp (Complex.I * (t : ℂ)) * Complex.I) *
          ((Complex.exp (Complex.I * (t : ℂ)) - z)⁻¹ *
            f (Complex.exp (Complex.I * (t : ℂ)))) := by
  have hc := hf.circleIntegral_sub_inv_smul hz
  rw [apm_a98A07_circleIntegral_eq_parameterIntegral] at hc
  simp only [smul_eq_mul] at hc
  have hc' :
      (∫ t in Ioo (0 : ℝ) (2 * Real.pi),
        (Complex.exp (Complex.I * (t : ℂ)) * Complex.I) *
          ((Complex.exp (Complex.I * (t : ℂ)) - z)⁻¹ *
            f (Complex.exp (Complex.I * (t : ℂ))))) =
        (2 * Real.pi * Complex.I : ℂ) * f z := by
    simpa only [mul_assoc] using hc
  have hconst : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  rw [hc']
  field_simp

/-- The parameter-space Cauchy kernel on the unit circle. -/
noncomputable def apm_a98A07_cauchyKernel (z : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (Complex.I * (t : ℂ)) * Complex.I) *
    (Complex.exp (Complex.I * (t : ℂ)) - z)⁻¹

/-- The Cauchy transform of an integrable boundary function. -/
noncomputable def apm_a98A07_cauchyTransform (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ *
    ∫ t in Ioo (0 : ℝ) (2 * Real.pi), apm_a98A07_cauchyKernel z t * h t

lemma apm_a98A07_cauchyKernel_mul_bound {r : ℝ} (hr : r < 1) {z a : ℂ}
    (hz : ‖z‖ ≤ r) (t : ℝ) :
    ‖apm_a98A07_cauchyKernel z t * a‖ ≤ (1 - r)⁻¹ * ‖a‖ := by
  simpa only [apm_a98A07_cauchyKernel, norm_mul, Complex.norm_I, Complex.norm_exp,
    Complex.I_re, mul_zero, Complex.I_im, mul_one, zero_add,
    Real.exp_zero, one_mul, norm_inv, mul_assoc, mul_left_comm, mul_comm] using
    (apm_a98A07_cauchy_kernel_bound hr hz t (a := a))

/-- Quantitative reconstruction estimate: boundary `L¹` error controls the
error uniformly on a fixed closed subdisk. -/
lemma apm_a98A07_cauchyTransform_error {f : ℂ → ℂ} {h : ℝ → ℂ}
    (hf : DifferentiableOn ℂ f (closedBall 0 1))
    (hfint : Integrable (fun t : ℝ => f (Complex.exp (Complex.I * (t : ℂ))))
      ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))))
    (hh : Integrable h ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))))
    {r : ℝ} (hr : r < 1) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z - apm_a98A07_cauchyTransform h z‖ ≤
      ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (1 - r)⁻¹ *
        ∫ t in Ioo (0 : ℝ) (2 * Real.pi),
          ‖f (Complex.exp (Complex.I * (t : ℂ))) - h t‖ := by
  let mu : Measure ℝ := (volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))
  let F : ℝ → ℂ := fun t => f (Complex.exp (Complex.I * (t : ℂ)))
  have hzball : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    exact hz.trans_lt hr
  have hkcont : Continuous (apm_a98A07_cauchyKernel z) := by
    unfold apm_a98A07_cauchyKernel
    apply Continuous.mul
    · fun_prop
    · apply Continuous.inv₀
      · fun_prop
      · intro t heq
        have heq' : Complex.exp (Complex.I * (t : ℂ)) = z := sub_eq_zero.mp heq
        have : ‖z‖ = 1 := by rw [← heq']; simp [Complex.norm_exp]
        linarith
  have hkmeas : AEStronglyMeasurable (apm_a98A07_cauchyKernel z) mu :=
    hkcont.aestronglyMeasurable
  have hmul (u : ℝ → ℂ) (hu : Integrable u mu) :
      Integrable (fun t => apm_a98A07_cauchyKernel z t * u t) mu := by
    apply (hu.norm.const_mul (1 - r)⁻¹).mono' (hkmeas.mul hu.aestronglyMeasurable)
    filter_upwards with t
    simpa [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hr.le))] using
      (apm_a98A07_cauchyKernel_mul_bound hr hz t (a := u t))
  have hF : Integrable F mu := hfint
  have hKF := hmul F hF
  have hKh := hmul h hh
  have hdiff : Integrable (fun t => (1 - r)⁻¹ * ‖F t - h t‖) mu :=
    (hF.sub hh).norm.const_mul _
  have hformula : f z = (2 * Real.pi * Complex.I : ℂ)⁻¹ *
      ∫ t, apm_a98A07_cauchyKernel z t * F t ∂mu := by
    simpa [mu, F, apm_a98A07_cauchyKernel, mul_assoc] using
      (apm_a98A07_cauchy_parameter_formula hf hzball)
  rw [hformula]
  unfold apm_a98A07_cauchyTransform
  change ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ * (∫ t, apm_a98A07_cauchyKernel z t * F t ∂mu) -
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * (∫ t, apm_a98A07_cauchyKernel z t * h t ∂mu)‖ ≤ _
  rw [← mul_sub, ← integral_sub hKF hKh]
  calc
    ‖(2 * Real.pi * Complex.I : ℂ)⁻¹ *
        ∫ t, apm_a98A07_cauchyKernel z t * F t -
          apm_a98A07_cauchyKernel z t * h t ∂mu‖
        ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
          ‖∫ t, apm_a98A07_cauchyKernel z t * F t -
            apm_a98A07_cauchyKernel z t * h t ∂mu‖ := norm_mul_le _ _
    _ ≤ ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
          ∫ t, (1 - r)⁻¹ * ‖F t - h t‖ ∂mu := by
      gcongr
      apply norm_integral_le_of_norm_le hdiff
      filter_upwards with t
      simpa [mul_sub] using
        (apm_a98A07_cauchyKernel_mul_bound hr hz t (a := F t - h t))
    _ = _ := by
      change ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
          (∫ t, (1 - r)⁻¹ * ‖F t - h t‖ ∂mu) =
        ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (1 - r)⁻¹ *
          ∫ t, ‖F t - h t‖ ∂mu
      rw [MeasureTheory.integral_const_mul]
      ring

/-- Boundary `L¹` convergence implies uniform convergence on each fixed
closed subdisk to the Cauchy transform of the boundary limit. -/
lemma apm_a98A07_tendstoUniformlyOn_closedBall
    {f : ℕ → ℂ → ℂ} {h : ℝ → ℂ}
    (hf : ∀ n, DifferentiableOn ℂ (f n) (closedBall 0 1))
    (hfint : ∀ n, Integrable
      (fun t : ℝ => f n (Complex.exp (Complex.I * (t : ℂ))))
      ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))))
    (hh : Integrable h ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))))
    (hL1 : Tendsto (fun n => ∫ t in Ioo (0 : ℝ) (2 * Real.pi),
      ‖f n (Complex.exp (Complex.I * (t : ℂ))) - h t‖) atTop (𝓝 0))
    {r : ℝ} (hr : r < 1) :
    TendstoUniformlyOn f (apm_a98A07_cauchyTransform h) atTop (closedBall 0 r) := by
  rw [tendstoUniformlyOn_iff]
  intro ε hε
  let C : ℝ := ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (1 - r)⁻¹
  have ht : Tendsto (fun n => C * ∫ t in Ioo (0 : ℝ) (2 * Real.pi),
      ‖f n (Complex.exp (Complex.I * (t : ℂ))) - h t‖) atTop (𝓝 0) := by
    simpa using hL1.const_mul C
  have hev : ∀ᶠ n in atTop, C * ∫ t in Ioo (0 : ℝ) (2 * Real.pi),
      ‖f n (Complex.exp (Complex.I * (t : ℂ))) - h t‖ < ε :=
    (tendsto_order.1 ht).2 ε hε
  filter_upwards [hev] with n hn
  intro z hz
  have hz' : ‖z‖ ≤ r := by simpa [mem_closedBall] using hz
  have hb := apm_a98A07_cauchyTransform_error (hf n) (hfint n) hh hr hz'
  rw [dist_eq_norm]
  exact (by simpa [C, norm_sub_rev] using hb.trans_lt hn)

/-- The closed-subdisk estimates assemble into local uniform convergence on
the open unit disk. -/
lemma apm_a98A07_tendstoLocallyUniformlyOn_of_boundary_L1
    {f : ℕ → ℂ → ℂ} {h : ℝ → ℂ}
    (hf : ∀ n, DifferentiableOn ℂ (f n) (closedBall 0 1))
    (hfint : ∀ n, Integrable
      (fun t : ℝ => f n (Complex.exp (Complex.I * (t : ℂ))))
      ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))))
    (hh : Integrable h ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))))
    (hL1 : Tendsto (fun n => ∫ t in Ioo (0 : ℝ) (2 * Real.pi),
      ‖f n (Complex.exp (Complex.I * (t : ℂ))) - h t‖) atTop (𝓝 0)) :
    TendstoLocallyUniformlyOn f (apm_a98A07_cauchyTransform h) atTop (ball 0 1) := by
  rw [tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have hxnorm : ‖x‖ < 1 := by simpa [mem_ball] using hx
  let r : ℝ := (‖x‖ + 1) / 2
  have hxr : ‖x‖ < r := by dsimp [r]; linarith
  have hr : r < 1 := by dsimp [r]; linarith
  have hU := apm_a98A07_tendstoUniformlyOn_closedBall hf hfint hh hL1 hr
  rw [tendstoUniformlyOn_iff] at hU
  refine ⟨ball (0 : ℂ) r, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds ?_), ?_⟩
  · simpa [mem_ball] using hxr
  · filter_upwards [hU ε hε] with n hn
    intro y hy
    exact hn y (mem_closedBall'.2 (le_of_lt (by simpa [mem_ball] using hy)))

/-- Mathlib's Weierstrass theorem closes the final regularity step once local
uniform convergence on the disk has been constructed. -/
lemma apm_a98A07_differentiableOn_of_locallyUniform
    {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, DifferentiableOn ℂ (f n) (ball 0 1))
    (hconv : TendstoLocallyUniformlyOn f g atTop (ball 0 1)) :
    DifferentiableOn ℂ g (ball 0 1) := by
  exact hconv.differentiableOn (Eventually.of_forall hf) isOpen_ball

theorem apm_a98a07 :
    ∀ f : ℕ → ℂ → ℂ,
      (∃ U : Set ℂ,
        IsOpen U ∧ closedBall (0 : ℂ) 1 ⊆ U ∧
          ∀ n : ℕ, DifferentiableOn ℂ (f n) U) →
      (∀ (n : ℕ) (t : ℝ), 0 < t → t < 2 * Real.pi →
        ‖f n (Complex.exp (Complex.I * (t : ℂ)))‖ ≤
          1 / (t * (Real.log (t / (4 * Real.pi))) ^ 2)) →
      (∀ᵐ t : ℝ ∂((volume : Measure ℝ).restrict (Ioo (0 : ℝ) (2 * Real.pi))),
        ∃ w : ℂ,
          Tendsto (fun n : ℕ => f n (Complex.exp (Complex.I * (t : ℂ)))) atTop (𝓝 w)) →
      ∃ g : ℂ → ℂ,
        DifferentiableOn ℂ g (ball 0 1) ∧
        TendstoLocallyUniformlyOn f g atTop (ball 0 1) := by
  /-
  PARTIAL boundary (closer hop 3).

  `apm_a98A07_log_ratio_neg` now proves that
  `log (t/(4π)) < 0` throughout `(0,2π)`. This formally eliminates a second
  endpoint pole and isolates `t = 0` as the majorant's only singularity.

  Searches went beyond the original `Vitali` name: `LEMMA-INDEX.md`,
  `ConstructionTargets/`, closed artifacts, and Mathlib's locally-uniform,
  normal-family, compact-open, holomorphic-limit, Morera, Cauchy integral,
  Bochner dominated-convergence, and improper-log-integral sources contain no
  Vitali/Montel or Weierstrass convergence theorem matching
  `TendstoLocallyUniformlyOn`. Mathlib's Cauchy formula can reconstruct each
  `f n`, but the frozen boundary data are merely a.e. convergent under an L¹
  majorant, so closure still requires: prove integrability of
  `1/(t*log(t/(4π))²)` by logarithmic substitution; select a measurable a.e.
  limit; obtain L¹ convergence by DCT; establish a uniform Cauchy-kernel bound
  on each compact subdisk; and prove the locally uniform limit holomorphic.

  Related Hurwitz/Rouché artifacts (`a97J08`, `a94A09`) confirm the absence of
  the final holomorphic-limit pipeline, and git history has no later attempt.
  No statement defect was found.

  CLOSER HOP 2: the prior claim that Mathlib lacked the final holomorphic-limit
  pipeline is now obsolete. `Analysis.Complex.LocallyUniformLimit` provides
  `TendstoLocallyUniformlyOn.differentiableOn`, and sibling `a01A07` contains a
  compiled use of exactly that theorem. The helper
  `apm_a98A07_differentiableOn_of_locallyUniform` above adapts it to this unit
  disk, closing step 4 completely. The remaining bridge is now only steps 1--3:
  majorant integrability, boundary L¹ convergence, and the Cauchy-kernel bound
  producing local uniform convergence.

  CLOSER HOP 3: the displayed bound is now packaged as
  `apm_a98A07_majorant`. `apm_a98A07_majorant_measurable` proves its global
  measurability, and `apm_a98A07_majorant_pos` combines the strict logarithm
  sign from hop 1 with the positive parameter to prove strict positivity on
  `(0,2π)`. These discharge the measurability and sign obligations needed by
  dominated convergence. Searches of the improper-log-integral and
  one-dimensional substitution APIs still found no packaged evaluation of
  `1/(t*log(t/(4π))²)`; proving its integrability by `u = -log(t/(4π))`, then
  selecting the measurable a.e. limit and deriving the Cauchy-kernel bound,
  remains open.

  HOP 4: renewed inspection found the general one-dimensional Jacobian result
  `MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul` and the
  improper-integral substitution theorem
  `MeasureTheory.integral_comp_mul_deriv_Ioi`.  Neither closes the logarithmic
  substitution: the former leaves the transformed integrability obligation,
  while the latter assumes both integrability obligations.  The precise first
  missing lemma is

      Integrable apm_a98A07_majorant
        ((volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))).

  After that, the two independent interfaces needed by the existing proof are:

      ∀ {F : ℕ → ℝ → ℂ},
        (∀ n, AEStronglyMeasurable (F n) μ) →
        (∀ n, ∀ᵐ t ∂μ, ‖F n t‖ ≤ apm_a98A07_majorant t) →
        (∀ᵐ t ∂μ, ∃ w, Tendsto (fun n => F n t) atTop (𝓝 w)) →
        ∃ h, AEStronglyMeasurable h μ ∧
          Tendsto (fun n => ∫ t, ‖F n t - h t‖ ∂μ) atTop (𝓝 0)

  for `μ = volume.restrict (Ioo 0 (2 * Real.pi))`, and a Cauchy reconstruction
  lemma saying that this L¹ convergence of the boundary traces of functions
  holomorphic on a common neighborhood of the closed unit disk implies
  `∃ g, TendstoLocallyUniformlyOn f g atTop (ball 0 1)`.  The first is a
  standard measurable-limit plus dominated-convergence assembly; the second
  is the genuinely complex-analytic kernel estimate.  These statements are
  true and together feed directly into
  `apm_a98A07_differentiableOn_of_locallyUniform`.  No packaged declaration
  for either assembly was found in `LEMMA-INDEX.md`, `ConstructionTargets/`,
  the solved corpus, or Mathlib's dominated-convergence, Cauchy-integral,
  Jacobian, and improper-integral sources.  Thus outcomes A and B both remain
  open, with the frozen statement unchanged.

  HOP 5: outcome A is now closed. The logarithmic tail is proved integrable
  as the derivative of `-1/log x`, and the reciprocal Jacobian transports it
  to `apm_a98A07_majorant_integrable`. Canonical a.e. limit selection plus DCT
  now gives boundary L¹ convergence. On the analytic side, trace
  measurability, the exact unit-circle parameter form of Cauchy's formula, and
  the uniform Cauchy-kernel bound on every closed subdisk all compile. The
  dependent residual is to combine them into the integral difference
  estimate, define the Cauchy transform of the boundary limit, and discharge
  `TendstoLocallyUniformlyOn` through its compact-set criterion.
  -/
  intro f hcommon hbound hconv
  rcases hcommon with ⟨U, hUopen, hclosed, hfU⟩
  let mu : Measure ℝ := (volume : Measure ℝ).restrict (Ioo 0 (2 * Real.pi))
  let F : ℕ → ℝ → ℂ :=
    fun n t => f n (Complex.exp (Complex.I * (t : ℂ)))
  have hfclosed : ∀ n, DifferentiableOn ℂ (f n) (closedBall 0 1) :=
    fun n => (hfU n).mono hclosed
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact apm_a98A07_trace_aestronglyMeasurable (hfclosed n).continuousOn
  have hFbound : ∀ n, ∀ᵐ t ∂mu, ‖F n t‖ ≤ apm_a98A07_majorant t := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hbound n t ht.1 ht.2
  have hFlim : ∀ᵐ t ∂mu, Tendsto (fun n => F n t) atTop
      (𝓝 (apm_a98A07_aeLimit F t)) :=
    hconv.mono fun _ ht => apm_a98A07_tendsto_aeLimit ht
  have hmeas : AEStronglyMeasurable (apm_a98A07_aeLimit F) mu :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hFlim
  have hlimBound : ∀ᵐ t ∂mu,
      ‖apm_a98A07_aeLimit F t‖ ≤ apm_a98A07_majorant t := by
    filter_upwards [hFlim, eventually_countable_forall.2 hFbound] with t ht hb
    exact le_of_tendsto' ht.norm fun n => hb n
  have hh : Integrable (apm_a98A07_aeLimit F) mu :=
    apm_a98A07_majorant_integrable.mono' hmeas hlimBound
  have hfint : ∀ n, Integrable (F n) mu :=
    fun n => apm_a98A07_majorant_integrable.mono' (hFmeas n) (hFbound n)
  have hL1 : Tendsto (fun n => ∫ t, ‖F n t - apm_a98A07_aeLimit F t‖ ∂mu)
      atTop (𝓝 0) :=
    apm_a98A07_tendsto_integral_norm_sub hFmeas apm_a98A07_majorant_integrable
      hFbound hconv
  have hlocal : TendstoLocallyUniformlyOn f
      (apm_a98A07_cauchyTransform (apm_a98A07_aeLimit F)) atTop (ball 0 1) := by
    apply apm_a98A07_tendstoLocallyUniformlyOn_of_boundary_L1 hfclosed
    · exact hfint
    · exact hh
    · exact hL1
  refine ⟨apm_a98A07_cauchyTransform (apm_a98A07_aeLimit F), ?_, hlocal⟩
  exact apm_a98A07_differentiableOn_of_locallyUniform
    (fun n => (hfU n).mono fun _ hz => hclosed (ball_subset_closedBall hz)) hlocal
