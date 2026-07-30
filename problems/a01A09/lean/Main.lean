import Mathlib
import ApmCanaries.Frames.A01A09.Apm_v2_a01A09_1774988409275.Scratch

noncomputable section

namespace ApmCanaries.Frames.A01A09.Apm_v2_a01A09_1774988409275.Main

/- Authoritative frame-local Lean development.
   Keep exploratory detours in Scratch.lean.
   Promote reusable lemmas explicitly into ApmCanaries.Local. -/

open scoped Real MeasureTheory Topology

open Complex MeasureTheory Set Filter

lemma abs_exp_mul_real (z : ℂ) (t : ℝ) :
    ‖Complex.exp (z * (t : ℂ))‖ = Real.exp (z.re * t) := by
  simpa [Complex.norm_exp, Complex.mul_re, Complex.ofReal_im,
    Complex.ofReal_re, mul_comm, mul_left_comm, mul_assoc] using
    (Complex.norm_exp (z * (t : ℂ)))

/-- Absolute value of the Laplace kernel with the decaying `e^{-tz}` factor. -/
lemma abs_laplace_kernel (z : ℂ) (t : ℝ) :
    ‖Complex.exp (-(t : ℂ) * z)‖ = Real.exp (-z.re * t) := by
  simpa [neg_mul, abs_exp_mul_real, mul_comm] using
    abs_exp_mul_real (-z) t

/-- The closed half-line `[0,∞)` viewed as a measurable set. -/
def nonnegLine : Set ℝ := Set.Ici (0 : ℝ)

/-- Lebesgue measure restricted to `[0,∞)`. -/
def «μ₊» : Measure ℝ := volume.restrict nonnegLine

/-- Right half-plane where the Laplace integral converges. -/
def rightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

/-- Laplace kernel `t ↦ e^{-tz}`. -/
def laplaceKernel (z : ℂ) (t : ℝ) : ℂ := Complex.exp (-(t : ℂ) * z)

/-- Laplace transform of `f` evaluated at `z`. -/
def laplaceTransform (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t, f t * laplaceKernel z t ∂«μ₊»

/-- Package the standing hypotheses on `f`. -/
structure LaplaceData :=
  (p : ℝ)
  (hp : 1 < p)
  (f : ℝ → ℂ)
  (hf_meas : AEStronglyMeasurable f «μ₊»)
  (hf_lp : MemLp f (ENNReal.ofReal p) «μ₊»)

lemma laplace_deriv_bound_integrable (data : LaplaceData) {a : ℝ} (ha : 0 < a) :
    Integrable (fun t : ℝ => ‖data.f t‖ * (t * Real.exp (-a * t))) «μ₊» := by
  let q := data.p.conjExponent
  have hpq : data.p.HolderConjugate q :=
    Real.HolderConjugate.conjExponent data.hp
  letI : ENNReal.HolderConjugate (ENNReal.ofReal data.p) (ENNReal.ofReal q) :=
    hpq.ennrealOfReal
  have hq : 1 < q := hpq.symm.lt
  have hq0 : 0 < q := zero_lt_one.trans hq
  let decay : ℝ → ℝ := fun t => t * Real.exp (-a * t)
  have hdecay_meas : AEStronglyMeasurable decay «μ₊» := by
    dsimp [decay]
    fun_prop
  have hdecay_lp : MemLp decay (ENNReal.ofReal q) «μ₊» := by
    apply (integrable_norm_rpow_iff hdecay_meas
      (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal hq0.le]
    change Integrable (fun t : ℝ => ‖decay t‖ ^ q)
      (volume.restrict nonnegLine)
    rw [← IntegrableOn, nonnegLine,
      integrableOn_Ici_iff_integrableOn_Ioi (hb := by finiteness)]
    apply (integrableOn_congr_fun (s := Ioi (0 : ℝ)) ?_ measurableSet_Ioi).2
    · exact integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := q) (b := a * q) (by linarith) (by norm_num)
          (mul_pos ha hq0)
    intro t ht
    dsimp [decay]
    rw [abs_of_pos (mul_pos ht (Real.exp_pos _))]
    rw [Real.mul_rpow ht.le (Real.exp_pos _).le]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    simp only [Real.rpow_one]
    congr 1
    ring_nf
  have hprod :
      Integrable (fun t => data.f t * (decay t : ℂ)) «μ₊» :=
    data.hf_lp.integrable_mul hdecay_lp.ofReal
  refine hprod.norm.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  simp only [Complex.norm_mul, Complex.norm_real, decay]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg ht (Real.exp_pos _).le)]

/-- The Laplace integrand is absolutely integrable on vertical strips of the
right half-plane. -/
lemma laplace_integrand_integrable (data : LaplaceData) {z : ℂ}
    (hz : 0 < z.re) :
    Integrable (fun t => data.f t * laplaceKernel z t) «μ₊» := by
  classical
  let q := data.p.conjExponent
  have hpq : data.p.HolderConjugate q :=
    Real.HolderConjugate.conjExponent data.hp
  letI : ENNReal.HolderConjugate (ENNReal.ofReal data.p) (ENNReal.ofReal q) :=
    hpq.ennrealOfReal
  have hq : 1 < q := hpq.symm.lt
  have hk_meas :
      AEStronglyMeasurable (fun t => laplaceKernel z t) «μ₊» := by
    unfold laplaceKernel
    fun_prop
  have hk_lp :
      MemLp (fun t => laplaceKernel z t) (ENNReal.ofReal q) «μ₊» := by
    have hq0 : 0 < q := zero_lt_one.trans hq
    apply (integrable_norm_rpow_iff hk_meas
      (ENNReal.ofReal_ne_zero_iff.mpr hq0) ENNReal.ofReal_ne_top).1
    rw [ENNReal.toReal_ofReal hq0.le]
    change Integrable
      (fun t : ℝ => ‖laplaceKernel z t‖ ^ q)
      (volume.restrict nonnegLine)
    rw [← IntegrableOn]
    apply (integrableOn_Ici_iff_integrableOn_Ioi).2
    convert integrableOn_exp_mul_Ioi
      (a := -(z.re * q)) (neg_lt_zero.mpr (mul_pos hz hq0)) 0 using 1
    funext t
    change ‖Complex.exp (-(t : ℂ) * z)‖ ^ q =
      Real.exp (-(z.re * q) * t)
    rw [abs_laplace_kernel]
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 1
    ring
  simpa only [Pi.mul_apply] using data.hf_lp.integrable_mul hk_lp

/-- Main claim (part 1): the Laplace transform is analytic on the right half-plane. -/
theorem laplace_transform_analytic (data : LaplaceData) :
    AnalyticOn ℂ (laplaceTransform data.f) rightHalfPlane := by
  classical
  have hopen : IsOpen rightHalfPlane := by
    rw [show rightHalfPlane = Complex.re ⁻¹' Ioi 0 by rfl]
    exact isOpen_Ioi.preimage Complex.continuous_re
  rw [Complex.analyticOn_iff_differentiableOn hopen]
  intro z₀ hz₀
  have hz₀pos : 0 < z₀.re := hz₀
  let r := z₀.re / 2
  have hr : 0 < r := half_pos hz₀pos
  let a := z₀.re / 2
  have ha : 0 < a := half_pos hz₀pos
  let F : ℂ → ℝ → ℂ :=
    fun z t => data.f t * laplaceKernel z t
  let F' : ℂ → ℝ → ℂ :=
    fun z t => data.f t * (-(t : ℂ) * laplaceKernel z t)
  let bound : ℝ → ℝ :=
    fun t => ‖data.f t‖ * (t * Real.exp (-a * t))
  have hF_meas :
      ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) «μ₊» := by
    filter_upwards [] with z
    dsimp [F, laplaceKernel]
    exact data.hf_meas.mul (by fun_prop)
  have hF_int : Integrable (F z₀) «μ₊» := by
    simpa only [F] using laplace_integrand_integrable data hz₀pos
  have hF'_meas : AEStronglyMeasurable (F' z₀) «μ₊» := by
    dsimp [F', laplaceKernel]
    exact data.hf_meas.mul (by fun_prop)
  have hbound_int : Integrable bound «μ₊» := by
    simpa only [bound] using laplace_deriv_bound_integrable data ha
  have hbound :
      ∀ᵐ t ∂«μ₊», ∀ z ∈ Metric.ball z₀ r, ‖F' z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht z hz
    change 0 ≤ t at ht
    have hnorm : ‖z - z₀‖ < r := by
      simpa [dist_eq] using hz
    have habs : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
    have hre : a ≤ z.re := by
      dsimp [a, r] at hnorm ⊢
      change |z.re - z₀.re| ≤ ‖z - z₀‖ at habs
      have hneg : -|(z - z₀).re| ≤ (z - z₀).re := neg_abs_le _
      change -|z.re - z₀.re| ≤ z.re - z₀.re at hneg
      linarith
    have hexp :
        Real.exp (-z.re * t) ≤ Real.exp (-a * t) := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right (neg_le_neg hre) ht
      simpa [neg_mul] using hm
    dsimp [F', bound]
    rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_of_nonneg ht]
    change ‖data.f t‖ * (t * ‖Complex.exp (-(t : ℂ) * z)‖) ≤
      ‖data.f t‖ * (t * Real.exp (-a * t))
    rw [abs_laplace_kernel]
    gcongr
  have hdiff :
      ∀ᵐ t ∂«μ₊», ∀ z ∈ Metric.ball z₀ r,
        HasDerivAt (fun z => F z t) (F' z t) z := by
    filter_upwards [] with t z hz
    have hlin :
        HasDerivAt (fun w : ℂ => -(t : ℂ) * w) (-(t : ℂ)) z := by
      simpa using (hasDerivAt_id z).const_mul (-(t : ℂ))
    have he :=
      (Complex.hasDerivAt_exp (-(t : ℂ) * z)).comp z hlin
    dsimp [F, F', laplaceKernel]
    convert HasDerivAt.const_mul (data.f t) he using 1 <;> ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z₀ hr) hF_meas hF_int hF'_meas hbound
      hbound_int hdiff
  simpa [F, laplaceTransform] using
    hmain.2.differentiableAt.differentiableWithinAt

/-- Extra hypothesis ensuring the Laplace transform extends to an entire function. -/
def compactSupportOnHalfLine (f : ℝ → ℂ) : Prop :=
  IsCompact ((Function.support f) ∩ nonnegLine)

/-- Under compact support, the Laplace transform is entire (part 2). -/
theorem laplace_transform_entire_of_compact_support
    (f : ℝ → ℂ) (hf : compactSupportOnHalfLine f) :
    AnalyticOn ℂ (fun z => laplaceTransform f z) Set.univ := by
  classical
  let K := Function.support f ∩ nonnegLine
  have hK : IsCompact K := hf
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.exists_pos_norm_le
  by_cases hfint : Integrable f «μ₊»
  · rw [Complex.analyticOn_univ_iff_differentiable]
    intro z₀
    let F : ℂ → ℝ → ℂ :=
      fun z t => f t * laplaceKernel z t
    let F' : ℂ → ℝ → ℂ :=
      fun z t => f t * (-(t : ℂ) * laplaceKernel z t)
    let C := R * Real.exp ((|z₀.re| + 1) * R)
    let bound : ℝ → ℝ := fun t => C * ‖f t‖
    have hF_meas :
        ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) «μ₊» := by
      filter_upwards [] with z
      dsimp [F, laplaceKernel]
      exact hfint.aestronglyMeasurable.mul (by fun_prop)
    have hF_int : Integrable (F z₀) «μ₊» := by
      let C₀ := Real.exp (|z₀.re| * R)
      have hmeas : AEStronglyMeasurable (F z₀) «μ₊» := by
        dsimp [F, laplaceKernel]
        exact hfint.aestronglyMeasurable.mul (by fun_prop)
      have hdom :
          ∀ᵐ t ∂«μ₊», ‖F z₀ t‖ ≤ ‖(C₀ : ℂ) * f t‖ := by
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        change 0 ≤ t at ht
        by_cases hft : f t = 0
        · simp [F, hft]
        · have htK : t ∈ K := ⟨Function.mem_support.mpr hft, ht⟩
          have htR : |t| ≤ R := by
            simpa [Real.norm_eq_abs] using hR t htK
          have hk :
              ‖laplaceKernel z₀ t‖ ≤ C₀ := by
            dsimp [C₀]
            rw [show ‖laplaceKernel z₀ t‖ = Real.exp (-z₀.re * t) by
              change ‖Complex.exp (-(t : ℂ) * z₀)‖ = _
              exact abs_laplace_kernel z₀ t]
            apply Real.exp_le_exp.mpr
            calc
              -z₀.re * t ≤ |-z₀.re * t| := le_abs_self _
              _ = |z₀.re| * |t| := by rw [abs_mul, abs_neg]
              _ ≤ |z₀.re| * R :=
                mul_le_mul_of_nonneg_left htR (abs_nonneg _)
          dsimp [F]
          rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg
            (Real.exp_pos _).le]
          calc
            ‖f t‖ * ‖laplaceKernel z₀ t‖ ≤ ‖f t‖ * C₀ :=
              mul_le_mul_of_nonneg_left hk (norm_nonneg _)
            _ = C₀ * ‖f t‖ := by ring
      exact (hfint.const_mul (C₀ : ℂ)).mono hmeas hdom
    have hF'_meas : AEStronglyMeasurable (F' z₀) «μ₊» := by
      dsimp [F', laplaceKernel]
      exact hfint.aestronglyMeasurable.mul (by fun_prop)
    have hbound_int : Integrable bound «μ₊» := by
      dsimp [bound]
      exact hfint.norm.const_mul C
    have hbound :
        ∀ᵐ t ∂«μ₊», ∀ z ∈ Metric.ball z₀ 1, ‖F' z t‖ ≤ bound t := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht z hz
      change 0 ≤ t at ht
      by_cases hft : f t = 0
      · simp [F', bound, hft]
      · have htK : t ∈ K := ⟨Function.mem_support.mpr hft, ht⟩
        have htR : |t| ≤ R := by
          simpa [Real.norm_eq_abs] using hR t htK
        have hzre : |z.re| ≤ |z₀.re| + 1 := by
          have hnorm : ‖z - z₀‖ < 1 := by simpa [dist_eq] using hz
          have habs : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
          change |z.re - z₀.re| ≤ ‖z - z₀‖ at habs
          exact (abs_le.2 ⟨by
            have := neg_le_of_abs_le (habs.trans hnorm.le)
            linarith [neg_abs_le z₀.re], by
            have := le_of_abs_le (habs.trans hnorm.le)
            linarith [le_abs_self z₀.re]⟩)
        have hexp :
            Real.exp (-z.re * t) ≤
              Real.exp ((|z₀.re| + 1) * R) := by
          apply Real.exp_le_exp.mpr
          calc
            -z.re * t ≤ |-z.re * t| := le_abs_self _
            _ = |z.re| * |t| := by rw [abs_mul, abs_neg]
            _ ≤ (|z₀.re| + 1) * R :=
              mul_le_mul hzre htR (abs_nonneg _) (by positivity)
        dsimp [F', bound, C]
        rw [norm_mul, norm_mul, norm_neg, norm_real, Real.norm_of_nonneg ht]
        change ‖f t‖ * (t * ‖Complex.exp (-(t : ℂ) * z)‖) ≤
          R * Real.exp ((|z₀.re| + 1) * R) * ‖f t‖
        rw [abs_laplace_kernel]
        calc
          ‖f t‖ * (t * Real.exp (-z.re * t))
              ≤ ‖f t‖ * (R * Real.exp ((|z₀.re| + 1) * R)) := by
                gcongr
                exact (le_abs_self t).trans htR
          _ = R * Real.exp ((|z₀.re| + 1) * R) * ‖f t‖ := by ring
    have hdiff :
        ∀ᵐ t ∂«μ₊», ∀ z ∈ Metric.ball z₀ 1,
          HasDerivAt (fun z => F z t) (F' z t) z := by
      filter_upwards [] with t z hz
      have hlin :
          HasDerivAt (fun w : ℂ => -(t : ℂ) * w) (-(t : ℂ)) z := by
        simpa using (hasDerivAt_id z).const_mul (-(t : ℂ))
      have he :=
        (Complex.hasDerivAt_exp (-(t : ℂ) * z)).comp z hlin
      dsimp [F, F', laplaceKernel]
      convert HasDerivAt.const_mul (f t) he using 1 <;> ring
    have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Metric.ball_mem_nhds z₀ zero_lt_one) hF_meas hF_int hF'_meas
        hbound hbound_int hdiff
    simpa [F, laplaceTransform] using hmain.2.differentiableAt
  · have hnotprod : ∀ z : ℂ,
        ¬ Integrable (fun t => f t * laplaceKernel z t) «μ₊» := by
      intro z hprod
      apply hfint
      have hinv_meas :
          AEStronglyMeasurable
            (fun t : ℝ => Complex.exp ((t : ℂ) * z)) «μ₊» := by
        fun_prop
      have hrecover :
          f =ᵐ[«μ₊»]
            (fun t => (f t * laplaceKernel z t) *
              Complex.exp ((t : ℂ) * z)) := by
        filter_upwards [] with t
        dsimp [laplaceKernel]
        rw [mul_assoc, ← Complex.exp_add]
        ring_nf
        simp
      have hf_meas : AEStronglyMeasurable f «μ₊» :=
        (hprod.aestronglyMeasurable.mul hinv_meas).congr hrecover.symm
      let C := Real.exp (|z.re| * R)
      have hdom :
          ∀ᵐ t ∂«μ₊»,
            ‖f t‖ ≤ ‖(C : ℂ) * (f t * laplaceKernel z t)‖ := by
        filter_upwards [ae_restrict_mem measurableSet_Ici, hrecover] with t ht hrec
        change 0 ≤ t at ht
        by_cases hft : f t = 0
        · simp [hft]
        · have htK : t ∈ K := ⟨Function.mem_support.mpr hft, ht⟩
          have htR : |t| ≤ R := by
            simpa [Real.norm_eq_abs] using hR t htK
          have hinv :
              ‖Complex.exp ((t : ℂ) * z)‖ ≤ C := by
            dsimp [C]
            rw [Complex.norm_exp]
            apply Real.exp_le_exp.mpr
            rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
            simp only [zero_mul, sub_zero]
            calc
              t * z.re ≤ |t * z.re| := le_abs_self _
              _ = |z.re| * |t| := by rw [abs_mul, mul_comm]
              _ ≤ |z.re| * R :=
                mul_le_mul_of_nonneg_left htR (abs_nonneg _)
          have heq :
              f t = (f t * laplaceKernel z t) *
                Complex.exp ((t : ℂ) * z) := hrec
          calc
            ‖f t‖ =
                ‖(f t * laplaceKernel z t) *
                  Complex.exp ((t : ℂ) * z)‖ := congrArg norm heq
            _ = ‖f t * laplaceKernel z t‖ *
                  ‖Complex.exp ((t : ℂ) * z)‖ := norm_mul _ _
            _ ≤ ‖f t * laplaceKernel z t‖ * C :=
              mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
            _ = ‖(C : ℂ) * (f t * laplaceKernel z t)‖ := by
              have hnormC : ‖(C : ℂ)‖ = C := by
                exact (Complex.norm_real C).trans (abs_of_pos (Real.exp_pos _))
              calc
                ‖f t * laplaceKernel z t‖ * C =
                    ‖(C : ℂ)‖ * ‖f t * laplaceKernel z t‖ := by rw [hnormC]; ring
                _ = ‖(C : ℂ) * (f t * laplaceKernel z t)‖ :=
                  (norm_mul _ _).symm
      exact (hprod.const_mul (C : ℂ)).mono hf_meas hdom
    have hzero : (fun z => laplaceTransform f z) = fun _ => 0 := by
      funext z
      exact integral_undef (hnotprod z)
    rw [hzero]
    exact analyticOn_const

end ApmCanaries.Frames.A01A09.Apm_v2_a01A09_1774988409275.Main
