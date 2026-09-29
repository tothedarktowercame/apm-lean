import Mathlib

/-!
# APM m99J03

## Statement repairs

In part (a), the second condition `x ≤ 1/n` is repaired to `|x| ≤ 1/n`.
As printed, it overlaps the first condition whenever `x < -1/n`; the symmetric
absolute-value condition is the unique reading consistent with the stated piecewise
function and the supplied solution.

## Encoding questions

Convergence in `𝒟'(ℝ)` is encoded by its defining weak condition: convergence of
the associated integral against every smooth compactly supported test function.
-/

noncomputable section

def apm_m99j03_IsTestFunction (φ : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ

def apm_m99j03_triangle (n : ℕ) (x : ℝ) : ℝ :=
  if |x| > 1 / (n : ℝ) then 0
  else (n : ℝ) * (1 - (n : ℝ) * |x|)

def apm_m99j03_dipole (n : ℕ) (x : ℝ) : ℝ :=
  if -(1 / (n : ℝ)) < x ∧ x < 0 then (n : ℝ) ^ 2
  else if 0 ≤ x ∧ x ≤ 1 / (n : ℝ) then -((n : ℝ) ^ 2)
  else 0

/-- The triangular kernel is the unit profile transported by the dilation
`x ↦ n*x`, including its normalizing Jacobian factor. -/
lemma apm_m99j03_triangle_eq_scaled_profile {n : ℕ} (hn : 0 < n) (x : ℝ) :
    apm_m99j03_triangle n x =
      (n : ℝ) * apm_m99j03_triangle 1 ((n : ℝ) * x) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have habs : |(n : ℝ) * x| = (n : ℝ) * |x| := by
    rw [abs_mul, abs_of_pos hnR]
  have hscale : |(n : ℝ) * x| > 1 ↔ |x| > 1 / (n : ℝ) := by
    have hinv : (1 / (n : ℝ)) * n = 1 := by field_simp
    constructor
    · intro h
      rw [habs] at h
      nlinarith
    · intro h
      rw [habs]
      nlinarith
  unfold apm_m99j03_triangle
  simp only [Nat.cast_one, one_div_one]
  by_cases hx : |x| > 1 / (n : ℝ)
  · have hnx := hscale.mpr hx
    rw [if_pos hx, if_pos hnx]
    simp
  · have hnx : ¬|(n : ℝ) * x| > 1 := not_congr hscale |>.mpr hx
    rw [if_neg hx, if_neg hnx]
    simp [habs]

/-- A continuous max-form for the unit triangular profile. -/
lemma apm_m99j03_triangle_one_eq_max (x : ℝ) :
    apm_m99j03_triangle 1 x = max (1 - |x|) 0 := by
  unfold apm_m99j03_triangle
  simp only [Nat.cast_one, one_div_one, one_mul]
  by_cases hx : |x| > 1
  · rw [if_pos hx, max_eq_right]
    linarith
  · rw [if_neg hx, max_eq_left]
    linarith

lemma apm_m99j03_triangle_one_continuous :
    Continuous (apm_m99j03_triangle 1) := by
  rw [show apm_m99j03_triangle 1 = fun x => max (1 - |x|) 0 by
    funext x
    exact apm_m99j03_triangle_one_eq_max x]
  fun_prop

lemma apm_m99j03_triangle_one_hasCompactSupport :
    HasCompactSupport (apm_m99j03_triangle 1) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  rw [Function.mem_support] at hx
  have hle : |x| ≤ 1 := by
    by_contra h
    have hgt : |x| > 1 := lt_of_not_ge h
    apply hx
    simp [apm_m99j03_triangle, hgt]
  exact (abs_le.mp hle)

/-- The unit triangular profile has total mass one. -/
lemma apm_m99j03_integral_triangle_one :
    (∫ x : ℝ, apm_m99j03_triangle 1 x) = 1 := by
  have hint : MeasureTheory.Integrable (apm_m99j03_triangle 1) :=
    apm_m99j03_triangle_one_continuous.integrable_of_hasCompactSupport
      apm_m99j03_triangle_one_hasCompactSupport
  have hleft : (∫ x : ℝ in (-1)..0, apm_m99j03_triangle 1 x) = 1 / 2 := by
    have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume (-1) 0 :=
      continuous_const.intervalIntegrable _ _
    have hxint : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume (-1) 0 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 + x)]
    · rw [intervalIntegral.integral_add hc hxint,
        intervalIntegral.integral_const, integral_id]
      norm_num
    · intro x hx
      simp only [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · rw [apm_m99j03_triangle_one_eq_max, abs_of_nonpos hx.2]
        simp [show 0 ≤ 1 + x by linarith]
      · exfalso; linarith
  have hright : (∫ x : ℝ in 0..1, apm_m99j03_triangle 1 x) = 1 / 2 := by
    have hc : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
      continuous_const.intervalIntegrable _ _
    have hxint : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
      continuous_id.intervalIntegrable _ _
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => 1 - x)]
    · rw [intervalIntegral.integral_sub hc hxint,
        intervalIntegral.integral_const, integral_id]
      norm_num
    · intro x hx
      simp only [Set.mem_uIcc] at hx
      rcases hx with hx | hx
      · rw [apm_m99j03_triangle_one_eq_max, abs_of_nonneg hx.1]
        simp [sub_nonneg.mpr hx.2]
      · exfalso; linarith
  have hinterval : (∫ x : ℝ in (-1)..1, apm_m99j03_triangle 1 x) = 1 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hint.intervalIntegrable) (hint.intervalIntegrable), hleft, hright]
    norm_num
  have hcompl : (∫ x : ℝ in (Set.Icc (-1 : ℝ) 1)ᶜ,
      apm_m99j03_triangle 1 x) = 0 := by
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc.compl] with x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have habs : |x| > 1 := by rw [abs_of_neg (by linarith)]; linarith
      simp [apm_m99j03_triangle, habs]
    · have habs : |x| > 1 := by rw [abs_of_pos (by linarith)]; exact hx
      simp [apm_m99j03_triangle, habs]
  have hadd := MeasureTheory.integral_add_compl
    (s := Set.Icc (-1 : ℝ) 1) measurableSet_Icc hint
  have hset : (∫ x : ℝ in Set.Icc (-1 : ℝ) 1,
      apm_m99j03_triangle 1 x) = 1 := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hinterval
  rw [hset, hcompl] at hadd
  linarith

lemma apm_m99j03_dilation_integrable
    (ψ φ : ℝ → ℝ) (hψ : Continuous ψ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) (n : ℕ) :
    MeasureTheory.Integrable (fun x : ℝ => ψ (x / (n : ℝ)) * φ x) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hψ.comp (continuous_id.div_const (n : ℝ))).mul hφ
  · exact hφc.mul_left

/-- Dilation of a continuous profile converges weakly against a compactly
supported continuous function. -/
lemma apm_m99j03_dilation_tendsto
    (ψ φ : ℝ → ℝ) (hψ : Continuous ψ) (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x : ℝ, ψ (x / (n : ℝ)) * φ x)
      Filter.atTop (nhds (ψ 0 * ∫ x : ℝ, φ x)) := by
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : ℝ) R).bddAbove_image hψ.norm.continuousOn
  have hdom : ∀ n : ℕ, ∀ x : ℝ,
      ‖ψ (x / (n : ℝ)) * φ x‖ ≤ C * ‖φ x‖ := by
    intro n x
    by_cases hx : x ∈ Function.support φ
    · have hxt : x ∈ tsupport φ := subset_closure hx
      have hxR : x ∈ Metric.closedBall (0 : ℝ) R := hR hxt
      have hdivR : x / (n : ℝ) ∈ Metric.closedBall (0 : ℝ) R := by
        rw [Metric.mem_closedBall, dist_zero_right] at hxR ⊢
        by_cases hn : n = 0
        · have hR0 : 0 ≤ R := (norm_nonneg x).trans hxR
          simpa [hn] using hR0
        · rw [norm_div]
          have hn1 : 1 ≤ ‖(n : ℝ)‖ := by
            simpa [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using
              (Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn) : (1 : ℝ) ≤ n)
          exact (div_le_self (norm_nonneg x) hn1).trans hxR
      calc
        ‖ψ (x / (n : ℝ)) * φ x‖ = ‖ψ (x / (n : ℝ))‖ * ‖φ x‖ := norm_mul _ _
        _ ≤ C * ‖φ x‖ := mul_le_mul_of_nonneg_right
          (hC ⟨_, hdivR, rfl⟩) (norm_nonneg _)
    · simp only [Function.mem_support] at hx
      have hx0 : φ x = 0 := not_ne_iff.mp hx
      simp [hx0]
  have hmeas : ∀ n : ℕ,
      MeasureTheory.AEStronglyMeasurable (fun x : ℝ => ψ (x / (n : ℝ)) * φ x) :=
    fun n => ((hψ.comp (continuous_id.div_const (n : ℝ))).mul hφ).aestronglyMeasurable
  have hmajor : MeasureTheory.Integrable (fun x : ℝ => C * ‖φ x‖) := by
    exact (hφ.norm.integrable_of_hasCompactSupport hφc.norm).const_mul C
  have hlim : ∀ᵐ x : ℝ,
      Filter.Tendsto (fun n : ℕ => ψ (x / (n : ℝ)) * φ x)
        Filter.atTop (nhds (ψ 0 * φ x)) := by
    filter_upwards [] with x
    exact (hψ.continuousAt.tendsto.comp
      (tendsto_const_div_atTop_nhds_zero_nat x)).mul tendsto_const_nhds
  have hi := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun x : ℝ => C * ‖φ x‖) hmeas hmajor
    (fun n => Filter.Eventually.of_forall (hdom n)) hlim
  simpa [MeasureTheory.integral_const_mul] using hi

/-- Why this unblocks `apm_m99j03`: this is the final change-of-variables
assembly for the normalized triangular approximate identity.  The profile
scaling and its unit mass are already proved above. -/
theorem apm_m99J03_bridge_triangle_weak_limit
    (φ : ℝ → ℝ) (hφ : apm_m99j03_IsTestFunction φ) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x : ℝ, apm_m99j03_triangle n x * φ x)
      Filter.atTop (nhds (φ 0)) := by
  have ht := apm_m99j03_dilation_tendsto φ (apm_m99j03_triangle 1)
    hφ.1.continuous apm_m99j03_triangle_one_continuous
    apm_m99j03_triangle_one_hasCompactSupport
  have ht' : Filter.Tendsto
      (fun n : ℕ => ∫ y : ℝ, φ (y / (n : ℝ)) * apm_m99j03_triangle 1 y)
      Filter.atTop (nhds (φ 0)) := by
    simpa [apm_m99j03_integral_triangle_one] using ht
  apply ht'.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  let g : ℝ → ℝ := fun y =>
    apm_m99j03_triangle 1 y * φ (y / (n : ℝ))
  have hchange := MeasureTheory.Measure.integral_comp_mul_left g (n : ℝ)
  have habsinv : |((n : ℝ)⁻¹)| = (n : ℝ)⁻¹ := abs_of_pos (inv_pos.mpr hnR)
  have hscaled :
      (∫ x : ℝ, apm_m99j03_triangle n x * φ x) =
        (n : ℝ) * ∫ x : ℝ, g ((n : ℝ) * x) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    rw [apm_m99j03_triangle_eq_scaled_profile hn x]
    simp only [g]
    have hx : (n : ℝ) * x / (n : ℝ) = x := by field_simp
    rw [hx]
    ring
  rw [hscaled, hchange, habsinv]
  simp only [smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hn0, one_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  simp only [g]
  ring

/-- Why this unblocks `apm_m99j03`: this is the exact scaling and cancellation
identity for the dipole.  It reduces the raw piecewise whole-line integral to
the symmetric first difference on the fixed interval `[0,1]`. -/
theorem apm_m99J03_bridge_dipole_integral_eq
    (φ : ℝ → ℝ) (hφ : apm_m99j03_IsTestFunction φ)
    (n : ℕ) (hn : 0 < n) :
    (∫ x : ℝ, apm_m99j03_dipole n x * φ x) =
      (n : ℝ) * ∫ t in (0 : ℝ)..1,
        (φ (-(t / (n : ℝ))) - φ (t / (n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hφint : MeasureTheory.Integrable φ :=
    hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
  let a : ℝ := 1 / (n : ℝ)
  let left : ℝ → ℝ := Set.Ioo (-a) 0 |>.indicator
    (fun x => (n : ℝ) ^ 2 * φ x)
  let right : ℝ → ℝ := Set.Icc 0 a |>.indicator
    (fun x => -((n : ℝ) ^ 2) * φ x)
  have hleft : MeasureTheory.Integrable left := by
    exact (hφint.const_mul ((n : ℝ) ^ 2)).indicator measurableSet_Ioo
  have hright : MeasureTheory.Integrable right := by
    exact (hφint.const_mul (-((n : ℝ) ^ 2))).indicator measurableSet_Icc
  have hfun : (fun x : ℝ => apm_m99j03_dipole n x * φ x) = left + right := by
    funext x
    unfold left right a apm_m99j03_dipole
    simp only [Set.indicator, Set.mem_Ioo, Set.mem_Icc, Pi.add_apply]
    split_ifs <;> simp_all <;> try linarith
  have hraw :
      (∫ x : ℝ, apm_m99j03_dipole n x * φ x) =
        (n : ℝ) ^ 2 *
          ((∫ x in (-(1 / (n : ℝ)))..0, φ x) -
            ∫ x in (0 : ℝ)..(1 / (n : ℝ)), φ x) := by
    rw [hfun]
    change (∫ x : ℝ, left x + right x) = _
    rw [MeasureTheory.integral_add hleft hright]
    simp only [left, right, MeasureTheory.integral_indicator measurableSet_Ioo,
      MeasureTheory.integral_indicator measurableSet_Icc]
    rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Icc_eq_integral_Ioc]
    rw [← intervalIntegral.integral_of_le (by
          have := one_div_pos.mpr hnR
          linarith : -(1 / (n : ℝ)) ≤ 0),
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    ring
  rw [hraw]
  have hpos := intervalIntegral.integral_comp_div (f := φ)
    (a := (0 : ℝ)) (b := 1) hn0
  have hneg := intervalIntegral.integral_comp_div (f := φ)
    (a := (0 : ℝ)) (b := 1) (neg_ne_zero.mpr hn0)
  simp only [zero_div, one_div, smul_eq_mul] at hpos hneg
  have hiNeg : IntervalIntegrable (fun t : ℝ => φ (-(t / (n : ℝ))))
      MeasureTheory.volume 0 1 := by
    exact (hφ.1.continuous.comp
      (continuous_id.div_const (n : ℝ)).neg).intervalIntegrable _ _
  have hiPos : IntervalIntegrable (fun t : ℝ => φ (t / (n : ℝ)))
      MeasureTheory.volume 0 1 := by
    exact (hφ.1.continuous.comp (continuous_id.div_const (n : ℝ))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hiNeg hiPos]
  rw [show (fun t : ℝ => φ (-(t / (n : ℝ)))) =
      fun t : ℝ => φ (t / (-(n : ℝ))) by
        funext t; congr 1; field_simp]
  rw [hpos, hneg]
  rw [intervalIntegral.integral_symm]
  ring

lemma apm_m99j03_symmetric_difference_tendsto
    (A : ℝ → ℝ) {d : ℝ} (hA : HasDerivAt A d 0) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) *
        (A (-(1 / (n : ℝ))) - A (1 / (n : ℝ))))
      Filter.atTop (nhds (-2 * d)) := by
  have hp : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      Filter.atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_const_div_atTop_nhds_zero_nat 1, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    simp [Nat.ne_of_gt hn]
  have hm : Filter.Tendsto (fun n : ℕ => -(1 / (n : ℝ)))
      Filter.atTop (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa only [neg_zero] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).neg, ?_⟩
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    simp [Nat.ne_of_gt hn]
  have hsp := hA.tendsto_slope_zero.comp hp
  have hsm := hA.tendsto_slope_zero.comp hm
  have hsums : Filter.Tendsto
      (fun n : ℕ => -(slope A 0 (-(1 / (n : ℝ))) +
        slope A 0 (1 / (n : ℝ))))
      Filter.atTop (nhds (-2 * d)) := by
    convert (hsm.add hsp).neg using 1
    · funext n
      simp only [Function.comp_apply, slope, zero_add, smul_eq_mul]
      simp only [vsub_eq_sub]
      ring
    · ring
  apply hsums.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [slope, zero_add, smul_eq_mul]
  field_simp
  simp only [vsub_eq_sub]
  ring

def apm_m99j03_average (φ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, φ (s * t)

/-- The remaining parametric-integral calculation: differentiation under the
fixed finite interval gives the first moment `∫₀¹ t = 1/2`. -/
theorem apm_m99j03_average_hasDerivAt
    (φ : ℝ → ℝ) (hφ : apm_m99j03_IsTestFunction φ) :
    HasDerivAt (apm_m99j03_average φ) (deriv φ 0 / 2) 0 := by
  have hdcont : Continuous (deriv φ) := hφ.1.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image hdcont.norm.continuousOn
  have hC0 : 0 ≤ C := by
    have hz : (0 : ℝ) ∈ Set.Icc (-1) 1 := by norm_num
    exact (norm_nonneg (deriv φ 0)).trans (hC ⟨0, hz, rfl⟩)
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)
  let F : ℝ → ℝ → ℝ := fun s t => φ (s * t)
  let F' : ℝ → ℝ → ℝ := fun s t => t * deriv φ (s * t)
  have hs : Set.Icc (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := by
    exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)) (by
      intro x hx
      rw [Metric.mem_ball, Real.dist_eq] at hx
      have h := abs_lt.mp hx
      constructor <;> linarith)
  have hmeas : ∀ᶠ s in nhds (0 : ℝ),
      MeasureTheory.AEStronglyMeasurable (F s) μ := by
    filter_upwards [] with s
    exact (hφ.1.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  have hFint : MeasureTheory.Integrable (F 0) μ := by
    have : F 0 = fun _ : ℝ => φ 0 := by funext t; simp [F]
    rw [this]
    exact MeasureTheory.integrable_const _
  have hF'meas : MeasureTheory.AEStronglyMeasurable (F' 0) μ := by
    exact (continuous_id.mul (hdcont.comp
      (continuous_const.mul continuous_id))).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ s ∈ Set.Icc (-1 : ℝ) 1, ‖F' s t‖ ≤ C := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    intro s hsI
    have htI : t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
    have hst : s * t ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> nlinarith [hsI.1, hsI.2, htI.1, htI.2]
    have hdle : ‖deriv φ (s * t)‖ ≤ C := hC ⟨s * t, hst, rfl⟩
    simp only [F', Real.norm_eq_abs, abs_mul]
    have hat : |t| ≤ 1 := (abs_le.mpr htI)
    calc
      |t| * |deriv φ (s * t)| ≤ 1 * C :=
        mul_le_mul hat hdle (abs_nonneg _) (by norm_num)
      _ = C := one_mul C
  have hboundInt : MeasureTheory.Integrable (fun _ : ℝ => C) μ :=
    MeasureTheory.integrable_const C
  have hdiff : ∀ᵐ t ∂μ, ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      HasDerivAt (F · t) (F' s t) s := by
    filter_upwards with t
    intro s hsI
    convert (hφ.1.differentiable (by simp) (s * t)).hasDerivAt.comp s
      ((hasDerivAt_id s).mul_const t) using 1 <;> simp [F, F'] <;> ring
  obtain ⟨_, hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hmeas hFint hF'meas hbound hboundInt hdiff
  have hA : (fun s => ∫ t, F s t ∂μ) = apm_m99j03_average φ := by
    funext s
    change (∫ t in Set.Ioc (0 : ℝ) 1, F s t) = apm_m99j03_average φ s
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rfl
  have hD : (∫ t, F' 0 t ∂μ) = deriv φ 0 / 2 := by
    change (∫ t in Set.Ioc (0 : ℝ) 1, F' 0 t) = deriv φ 0 / 2
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simp only [F', zero_mul, mul_comm _ (deriv φ 0)]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  rw [hA, hD] at hderiv
  exact hderiv

/-- Why this unblocks `apm_m99j03`: this is the uniform first-order Taylor
remainder limit after dipole scaling.  Combined with the preceding exact
identity, it gives the second frozen convergence clause. -/
theorem apm_m99J03_bridge_dipole_scaled_difference_tendsto
    (φ : ℝ → ℝ) (hφ : apm_m99j03_IsTestFunction φ) :
    Filter.Tendsto
      (fun n : ℕ => (n : ℝ) * ∫ t in (0 : ℝ)..1,
        (φ (-(t / (n : ℝ))) - φ (t / (n : ℝ))))
      Filter.atTop (nhds (-deriv φ 0)) := by
  have hs := apm_m99j03_symmetric_difference_tendsto
    (apm_m99j03_average φ) (apm_m99j03_average_hasDerivAt φ hφ)
  have hs' : Filter.Tendsto
      (fun n : ℕ => (n : ℝ) *
        (apm_m99j03_average φ (-(1 / (n : ℝ))) -
          apm_m99j03_average φ (1 / (n : ℝ))))
      Filter.atTop (nhds (-deriv φ 0)) := by
    convert hs using 1 <;> ring
  apply hs'.congr'
  filter_upwards with n
  unfold apm_m99j03_average
  rw [← intervalIntegral.integral_sub]
  · apply congrArg ((n : ℝ) * ·)
    apply intervalIntegral.integral_congr
    intro t ht
    congr 2 <;> ring
  · exact (hφ.1.continuous.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  · exact (hφ.1.continuous.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _

theorem apm_m99j03
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
      Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, apm_m99j03_triangle n x * φ x)
        Filter.atTop (nhds (φ 0))) ∧
    (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
      Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, apm_m99j03_dipole n x * φ x)
        Filter.atTop (nhds (-deriv φ 0))) ∧
    ∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
      Filter.Tendsto
        (fun n : ℕ => ∫ x : ℝ, ψ (x / (n : ℝ)) * φ x)
        Filter.atTop (nhds (ψ 0 * ∫ x : ℝ, φ x)) := by
  have hab :
      (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
        Filter.Tendsto
          (fun n : ℕ => ∫ x : ℝ, apm_m99j03_triangle n x * φ x)
          Filter.atTop (nhds (φ 0))) ∧
      (∀ φ : ℝ → ℝ, apm_m99j03_IsTestFunction φ →
        Filter.Tendsto
          (fun n : ℕ => ∫ x : ℝ, apm_m99j03_dipole n x * φ x)
          Filter.atTop (nhds (-deriv φ 0))) := by
    refine ⟨apm_m99J03_bridge_triangle_weak_limit, ?_⟩
    intro φ hφ
    have hs := apm_m99J03_bridge_dipole_scaled_difference_tendsto φ hφ
    apply hs.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    exact (apm_m99J03_bridge_dipole_integral_eq φ hφ n hn).symm
  refine ⟨hab.1, hab.2, ?_⟩
  intro φ hφ
  exact apm_m99j03_dilation_tendsto ψ φ hψ.continuous hφ.1.continuous hφ.2
