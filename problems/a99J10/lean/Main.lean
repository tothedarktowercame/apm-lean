import Mathlib

/-!
# APM a99J10 — boundary uniqueness under square-root growth

## Statement repairs

The displayed bound `|f(x + iy)| ≤ |y|⁻¹ᐟ²` is singular when `y = 0`.
It is therefore imposed when `y ≠ 0`, which is the minimal domain restriction
needed to express the source's intended blow-up bound without assigning it a
spurious finite value on the real diameter.

## Encoding notes

The radial limit is expressed as `r → 1⁻` for every angle in `[0, 2π]`.
-/

open Set Filter MeasureTheory
open scoped Topology
open Metric

/-- Imaginary part of the standard radial parametrization. -/
lemma apm_a99J10_polar_im (r θ : ℝ) :
    (((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im) =
      r * Real.sin θ := by
  simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]

/-- A radius in `[0,1)` parametrizes a point of the open unit disk. -/
lemma apm_a99J10_polar_mem_ball {r θ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_zero_iff]
  rw [norm_mul, Complex.norm_exp]
  simpa [abs_of_nonneg hr0] using hr1

/-- The frozen growth hypothesis becomes an explicit angular majorant on
each circle. This is the input needed for a dominated boundary-limit route. -/
lemma apm_a99J10_polar_bound
    (f : ℂ → ℂ)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    {r θ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hsin : Real.sin θ ≠ 0) :
    ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      Real.rpow |r * Real.sin θ| (-(1 : ℝ) / 2) := by
  have hb := hbound ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
    (apm_a99J10_polar_mem_ball hr0.le hr1)
    (by rw [apm_a99J10_polar_im]; exact mul_ne_zero hr0.ne' hsin)
  simpa [apm_a99J10_polar_im] using hb

lemma apm_a99J10_integrable_rpow_neg_half :
    IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2))
      (Ioo 0 (Real.pi / 2)) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by positivity)]
  norm_num

lemma apm_a99J10_sin_rpow_le_first_quadrant
    {x : ℝ} (hx0 : 0 < x) (hxpi : x ≤ Real.pi / 2) :
    Real.rpow |Real.sin x| (-(1 : ℝ) / 2) ≤
      Real.rpow (2 / Real.pi * x) (-(1 : ℝ) / 2) := by
  have hlin : 0 < 2 / Real.pi * x := mul_pos (div_pos zero_lt_two Real.pi_pos) hx0
  have hsin : 2 / Real.pi * x ≤ |Real.sin x| :=
    (Real.mul_le_sin hx0.le hxpi).trans (le_abs_self _)
  exact Real.rpow_le_rpow_of_nonpos hlin hsin (by norm_num)

lemma apm_a99J10_intervalIntegrable_abs_sin_rpow_neg_half :
    IntervalIntegrable
      (fun θ : ℝ => Real.rpow |Real.sin θ| (-(1 : ℝ) / 2))
      volume 0 (2 * Real.pi) := by
  let g : ℝ → ℝ := fun θ => Real.rpow |Real.sin θ| (-(1 : ℝ) / 2)
  have hmodel : IntegrableOn (fun x : ℝ =>
      Real.rpow (2 / Real.pi * x) (-(1 : ℝ) / 2))
      (Ioo 0 (Real.pi / 2)) := by
    have hpow := apm_a99J10_integrable_rpow_neg_half
    have hc : IntegrableOn (fun x : ℝ =>
        Real.rpow (2 / Real.pi) (-(1 : ℝ) / 2) *
          Real.rpow x (-(1 : ℝ) / 2)) (Ioo 0 (Real.pi / 2)) :=
      hpow.const_mul _
    apply hc.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (Real.mul_rpow (by positivity) hx.1.le).symm
  have hqOn : IntegrableOn g (Ioo 0 (Real.pi / 2)) := by
    have hgmeas : AEStronglyMeasurable g
        (volume.restrict (Ioo 0 (Real.pi / 2))) := by
      apply ((continuous_abs.comp Real.continuous_sin).continuousOn.rpow_const
        (fun x hx => Or.inl ?_)).aestronglyMeasurable measurableSet_Ioo
      exact abs_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hx.1
        (lt_of_lt_of_le hx.2 (by linarith [Real.pi_pos]))).ne'
    apply hmodel.mono' hgmeas
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa [g, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg _ _)] using
      apm_a99J10_sin_rpow_le_first_quadrant hx.1 hx.2.le
  have hq : IntervalIntegrable g volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
    exact hqOn
  have h2 : IntervalIntegrable g volume (Real.pi / 2) Real.pi := by
    have h := (hq.comp_sub_left Real.pi).symm
    have h' : IntervalIntegrable (fun x => g (Real.pi - x)) volume
        (Real.pi / 2) Real.pi := by convert h using 1 <;> ring
    apply h'.congr
    intro x hx
    dsimp [g]
    rw [Real.sin_pi_sub]
  have h3 : IntervalIntegrable g volume Real.pi (3 * Real.pi / 2) := by
    have h := hq.comp_sub_right Real.pi
    have h' : IntervalIntegrable (fun x => g (x - Real.pi)) volume
        Real.pi (3 * Real.pi / 2) := by convert h using 1 <;> ring
    apply h'.congr
    intro x hx
    dsimp [g]
    rw [Real.sin_sub_pi, abs_neg]
  have h4 : IntervalIntegrable g volume (3 * Real.pi / 2) (2 * Real.pi) := by
    have h := (hq.comp_sub_left (2 * Real.pi)).symm
    have h' : IntervalIntegrable (fun x => g (2 * Real.pi - x)) volume
        (3 * Real.pi / 2) (2 * Real.pi) := by convert h using 1 <;> ring
    apply h'.congr
    intro x hx
    dsimp [g]
    rw [Real.sin_two_pi_sub, abs_neg]
  change IntervalIntegrable g volume 0 (2 * Real.pi)
  exact ((hq.trans h2).trans h3).trans h4

/-- For radii bounded below by `1/2`, the polar estimate has a single
radius-independent angular majorant.  This closes the uniform-domination
bookkeeping needed before applying dominated convergence. -/
lemma apm_a99J10_polar_bound_uniform
    (f : ℂ → ℂ)
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    {r θ : ℝ} (hr : (1 : ℝ) / 2 ≤ r) (hr1 : r < 1)
    (hsin : Real.sin θ ≠ 0) :
    ‖f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ≤
      Real.rpow ((1 : ℝ) / 2) (-(1 : ℝ) / 2) *
        Real.rpow |Real.sin θ| (-(1 : ℝ) / 2) := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  refine (apm_a99J10_polar_bound f hbound hr0 hr1 hsin).trans ?_
  rw [abs_mul, abs_of_pos hr0]
  change (r * |Real.sin θ|) ^ (-(1 : ℝ) / 2) ≤
    ((1 : ℝ) / 2) ^ (-(1 : ℝ) / 2) * |Real.sin θ| ^ (-(1 : ℝ) / 2)
  rw [Real.mul_rpow hr0.le (abs_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos (by norm_num) hr (by norm_num))
    (Real.rpow_nonneg (abs_nonneg _) _)

lemma apm_a99J10_cauchy_parameter_formula
    (f : ℂ → ℂ) {r : ℝ} (_hr0 : 0 < r) (hr1 : r < 1)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) r) :
    (∫ θ in Ioo (0 : ℝ) (2 * Real.pi),
      (((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I) *
        ((((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)⁻¹ *
          f ((r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) =
      (2 * Real.pi * Complex.I : ℂ) * f z := by
  have hclosed : closedBall (0 : ℂ) r ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff] at hw
    rw [mem_ball_zero_iff]
    exact hw.trans_lt hr1
  have hc := (hf.mono hclosed).circleIntegral_sub_inv_smul hz
  rw [circleIntegral, intervalIntegral.integral_of_le Real.two_pi_pos.le] at hc
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm] at hc
  simpa only [deriv_circleMap, circleMap_zero, smul_eq_mul, mul_assoc,
    mul_comm (Complex.I : ℂ)] using hc

set_option maxHeartbeats 800000 in
theorem apm_a99j10 (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbound : ∀ z ∈ ball (0 : ℂ) 1, z.im ≠ 0 →
      ‖f z‖ ≤ Real.rpow |z.im| (-(1 : ℝ) / 2))
    (hradial : ∀ θ ∈ Icc (0 : ℝ) (2 * Real.pi),
      Tendsto
        (fun r : ℝ => f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)))
        (𝓝[<] (1 : ℝ)) (𝓝 0)) :
    ∀ z ∈ ball (0 : ℂ) 1, f z = 0 := by
  intro z hz
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  let F : ℕ → ℝ → ℂ := fun n θ =>
    ((((r n : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) * Complex.I) *
      (((((r n : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)⁻¹ *
        f (((r n : ℝ) : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
  have hr_nhds : Tendsto r atTop (𝓝 (1 : ℝ)) := by
    simpa [r] using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have hr_tendsto : Tendsto r atTop (𝓝[<] (1 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hr_nhds, ?_⟩
    filter_upwards with n
    dsimp [r]
    have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    simpa only [mem_Iio] using sub_lt_self (1 : ℝ) this
  have hhalf : ∀ᶠ n in atTop, (1 : ℝ) / 2 ≤ r n := by
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    dsimp [r]
    have hn' : (2 : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hn 1
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hn'
    linarith
  have hrpos : ∀ᶠ n in atTop, 0 < r n := hhalf.mono fun _ h => lt_of_lt_of_le (by norm_num) h
  have hrlt : ∀ n, r n < 1 := by
    intro n
    dsimp [r]
    have : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith
  have hznorm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hzrad : ∀ᶠ n in atTop, ‖z‖ < r n := by
    exact (tendsto_order.1 hr_nhds).1 _ hznorm
  have hrnear : ∀ᶠ n in atTop, (1 + ‖z‖) / 2 < r n := by
    apply (tendsto_order.1 hr_nhds).1
    linarith
  have hFmeas : ∀ n, AEStronglyMeasurable (F n)
      (volume.restrict (uIoc (0 : ℝ) (2 * Real.pi))) := by
    intro n
    have hr0 : 0 ≤ r n := by
      dsimp [r]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      simpa using sub_nonneg.mpr (one_div_le_one_div_of_le zero_lt_one this)
    have hmap : ∀ θ : ℝ,
        ((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈ ball (0 : ℂ) 1 := by
      intro θ
      rw [mem_ball_zero_iff, norm_mul]
      simpa [Complex.norm_exp, Complex.mul_re, abs_of_nonneg hr0] using hrlt n
    have hp : Continuous (fun θ : ℝ =>
        (r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by fun_prop
    have hfcomp : Continuous (fun θ : ℝ =>
        f ((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :=
      hf.continuousOn.comp_continuous
        (by fun_prop) hmap
    dsimp [F]
    exact (((hp.mul_const Complex.I).measurable.mul
      ((measurable_inv.comp (hp.measurable.sub measurable_const)).mul
        hfcomp.measurable)).aestronglyMeasurable.restrict)
  have hang := apm_a99J10_intervalIntegrable_abs_sin_rpow_neg_half
  let C : ℝ := ((1 : ℝ) / 2) ^ (-(1 : ℝ) / 2) *
    (((1 - ‖z‖) / 2)⁻¹)
  have hdelta : 0 < (1 - ‖z‖) / 2 := by linarith
  have hCpos : 0 ≤ C :=
    mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (1 : ℝ) / 2) _)
      (inv_nonneg.mpr hdelta.le)
  have hsinAE : ∀ᵐ θ : ℝ ∂volume, Real.sin θ ≠ 0 := by
    have hc : {θ : ℝ | Real.sin θ = 0}.Countable := by
      apply (Set.countable_range (fun k : ℤ => (k : ℝ) * Real.pi)).mono
      intro θ hθ
      rcases Real.sin_eq_zero_iff.mp hθ with ⟨k, hk⟩
      exact ⟨k, hk⟩
    exact hc.ae_notMem volume
  have hboundF : ∀ᶠ n in atTop, ∀ᵐ θ ∂volume,
      θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
      ‖F n θ‖ ≤ C * Real.rpow |Real.sin θ| (-(1 : ℝ) / 2) := by
    filter_upwards [hhalf, hzrad, hrnear] with n hnhalf hnz hnnear
    filter_upwards [hsinAE] with θ hsin
    intro hθ
    have hfbd := apm_a99J10_polar_bound_uniform f hbound hnhalf (hrlt n) hsin
    have hdist : (1 - ‖z‖) / 2 ≤
        ‖((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z‖ := by
      calc
        (1 - ‖z‖) / 2 ≤ r n - ‖z‖ := by
          linarith
        _ = ‖((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ - ‖z‖ := by
          rw [norm_mul]
          simp [Complex.norm_exp, Complex.mul_re,
            abs_of_nonneg (le_trans (by norm_num) hnhalf)]
        _ ≤ _ := norm_sub_norm_le _ _
    have hinv : ‖(((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) - z)⁻¹‖ ≤
        ((1 - ‖z‖) / 2)⁻¹ := by
      rw [norm_inv]
      exact (inv_le_inv₀ (hdelta.trans_le hdist) hdelta).2 hdist
    dsimp [F, C]
    simp only [norm_mul]
    simp [Complex.norm_exp, Complex.mul_re,
      abs_of_nonneg (le_trans (by norm_num) hnhalf)]
    have hrle : r n ≤ 1 := (hrlt n).le
    have hinv' : ‖((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) - z)‖⁻¹ ≤
        2 / (1 - ‖z‖) := by
      simpa [div_eq_mul_inv] using hinv
    have hfbd' : ‖f ((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖ ≤
        2⁻¹ ^ (-(1 : ℝ) / 2) * |Real.sin θ| ^ (-(1 : ℝ) / 2) := by
      simpa [mul_comm (Complex.I : ℂ)] using hfbd
    have hquot : 0 ≤ 2 / (1 - ‖z‖) :=
      div_nonneg (by norm_num) (sub_nonneg.mpr hznorm.le)
    calc
      r n * (‖((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) - z)‖⁻¹ *
          ‖f ((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))‖) ≤
          1 * ((2 / (1 - ‖z‖)) *
            (2⁻¹ ^ (-(1 : ℝ) / 2) *
              |Real.sin θ| ^ (-(1 : ℝ) / 2))) := by gcongr
      _ = 2⁻¹ ^ (-(1 : ℝ) / 2) * (2 / (1 - ‖z‖)) *
          |Real.sin θ| ^ (-(1 : ℝ) / 2) := by ring
  have hlimF : ∀ᵐ θ ∂volume, θ ∈ uIoc (0 : ℝ) (2 * Real.pi) →
      Tendsto (fun n => F n θ) atTop (𝓝 0) := by
    filter_upwards with θ
    intro hθ
    rw [uIoc_of_le Real.two_pi_pos.le] at hθ
    have hrad := hradial θ ⟨hθ.1.le, hθ.2⟩
    have hzero := hrad.comp hr_tendsto
    have hzero' : Tendsto (fun n =>
        f ((r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) atTop (𝓝 0) := by
      simpa [Function.comp_def, mul_comm (Complex.I : ℂ)] using hzero
    have hpT : Tendsto (fun n =>
        (r n : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) atTop
        (𝓝 (Complex.exp (Complex.I * (θ : ℂ)))) := by
      simpa using hr_nhds.ofReal.mul_const
        (Complex.exp (Complex.I * (θ : ℂ)))
    have hne : Complex.exp (Complex.I * (θ : ℂ)) - z ≠ 0 := by
      intro heq
      have : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = ‖z‖ :=
        congrArg norm (sub_eq_zero.mp heq)
      have hexp : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
        simp [Complex.norm_exp, Complex.mul_re]
      linarith
    dsimp [F]
    convert ((hpT.mul_const Complex.I).mul
      (((hpT.sub tendsto_const_nhds).inv₀ hne).mul hzero')) using 1 <;> simp

  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (f := fun _ => (0 : ℂ))
    (fun θ => C * Real.rpow |Real.sin θ| (-(1 : ℝ) / 2))
    (Eventually.of_forall hFmeas) hboundF (hang.const_mul C) hlimF
  have hDCT' : Tendsto (fun n => ∫ θ in (0 : ℝ)..(2 * Real.pi), F n θ)
      atTop (𝓝 0) := by simpa using hDCT
  have hconst : Tendsto (fun _ : ℕ => (2 * Real.pi * Complex.I : ℂ) * f z)
      atTop (𝓝 0) := by
    apply hDCT'.congr' ?_
    filter_upwards [hrpos, hzrad] with n hn0 hnz
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
      Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm]
    simpa [F] using (apm_a99J10_cauchy_parameter_formula f hn0 (hrlt n) hf
      (by simpa [mem_ball_zero_iff] using hnz))
  simpa using tendsto_nhds_unique hconst tendsto_const_nhds

#print axioms apm_a99j10
