import Mathlib

/-! # APM m99A02: a logarithmic function in `H¹` of a planar disk

## Statement repairs

None.  The value assigned at the singleton `x = 0` is immaterial for both
Sobolev membership and distributional derivatives; it is set to zero below.

## Encoding note

Mathlib does not bundle Sobolev spaces.  Membership in `H¹(Ω)` is therefore
stated by its defining data: the function and its two displayed weak
derivatives lie in `L²(Ω)`, and each derivative satisfies the distributional
integration-by-parts identity against every compactly supported smooth test
function.
-/

open MeasureTheory Set
open Filter
open scoped ContDiff

noncomputable section

abbrev m99A02Point := EuclideanSpace ℝ (Fin 2)

def m99A02Omega : Set m99A02Point := Metric.ball 0 (1 / 2)

def m99A02Function (x : m99A02Point) : ℝ :=
  if x = 0 then 0 else (-Real.log ‖x‖) ^ (1 / 3 : ℝ)

def m99A02Derivative (i : Fin 2) (x : m99A02Point) : ℝ :=
  if x = 0 then 0
  else -(x i) / (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ))

def IsM99A02WeakDerivative
    (f g : m99A02Point → ℝ) (i : Fin 2) : Prop :=
  ∀ φ : m99A02Point → ℝ,
    ContDiff ℝ ∞ φ → HasCompactSupport φ → Function.support φ ⊆ m99A02Omega →
      (∫ x in m99A02Omega, f x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -∫ x in m99A02Omega, g x * φ x

/-- On the punctured domain the logarithmic base used by all real powers is positive. -/
lemma m99A02_neg_log_norm_pos {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    0 < -Real.log ‖x‖ := by
  have hr : ‖x‖ < (1 / 2 : ℝ) := by
    simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hx
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hr1 : ‖x‖ < 1 := hr.trans (by norm_num)
  exact neg_pos.mpr (Real.log_neg hr0 hr1)

/-- The chosen representative is strictly positive away from the singular point. -/
lemma m99A02Function_pos {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    0 < m99A02Function x := by
  rw [m99A02Function, if_neg hx0]
  exact Real.rpow_pos_of_pos (m99A02_neg_log_norm_pos hx hx0) _

/-- The singular representative is measurable; the exceptional value at the
origin is handled by a measurable singleton split. -/
lemma m99A02Function_measurable : Measurable m99A02Function := by
  unfold m99A02Function
  have hs : MeasurableSet {x : m99A02Point | x = 0} := by
    simpa only [setOf_eq_eq_singleton] using
      (measurableSet_singleton (0 : m99A02Point))
  apply Measurable.ite hs measurable_const
  exact (Real.continuous_rpow_const (by norm_num)).measurable.comp
    (Real.measurable_log.comp continuous_norm.measurable).neg

/-- Each displayed classical derivative is measurable as well. -/
lemma m99A02Derivative_measurable (i : Fin 2) :
    Measurable (m99A02Derivative i) := by
  unfold m99A02Derivative
  have hs : MeasurableSet {x : m99A02Point | x = 0} := by
    simpa only [setOf_eq_eq_singleton] using
      (measurableSet_singleton (0 : m99A02Point))
  apply Measurable.ite hs measurable_const
  fun_prop

/-- The sum of the squared displayed derivatives is the expected radial
Bertrand-integral density away from the origin. -/
lemma m99A02_sum_derivative_sq {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    ∑ i : Fin 2, (m99A02Derivative i x) ^ 2 =
      1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ)) := by
  have hr : ‖x‖ ≠ 0 := (norm_pos_iff.mpr hx0).ne'
  have hl : 0 < -Real.log ‖x‖ := m99A02_neg_log_norm_pos hx hx0
  simp_rw [m99A02Derivative, if_neg hx0]
  rw [show (∑ i : Fin 2, (-(x i) /
      (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ))) ^ 2) =
      (∑ i : Fin 2, (x i) ^ 2) /
        (3 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (2 / 3 : ℝ)) ^ 2 by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  rw [← EuclideanSpace.real_norm_sq_eq]
  have hlpow : ((-Real.log ‖x‖) ^ (2 / 3 : ℝ)) ^ 2 =
      (-Real.log ‖x‖) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hl.le]
    congr 1
    norm_num
  rw [mul_pow, mul_pow, hlpow]
  field_simp [hr, ne_of_gt hl]
  ring

/-- Each coordinate derivative is dominated by the single radial density. -/
lemma m99A02_derivative_sq_le_radial (i : Fin 2) {x : m99A02Point}
    (hx : x ∈ m99A02Omega) (hx0 : x ≠ 0) :
    (m99A02Derivative i x) ^ 2 ≤
      1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ)) := by
  rw [← m99A02_sum_derivative_sq hx hx0]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (m99A02Derivative j x))
    (Finset.mem_univ i)

/-- The scalar tail obtained from the logarithmic substitution
`u = -log r` in the derivative-energy radial integral is integrable. -/
lemma m99A02_integrable_log_tail :
    IntegrableOn (fun u : ℝ ↦ u ^ (-(4 / 3 : ℝ)))
      (Ioi (Real.log 2)) volume := by
  apply integrableOn_Ioi_rpow_of_lt
  · norm_num
  · exact Real.log_pos one_lt_two

/-- The additive-Haar polar criterion specialized to the Euclidean plane. -/
lemma m99A02_integrable_radial_iff {g : ℝ → ℝ} :
    Integrable (fun x : m99A02Point ↦ g ‖x‖) volume ↔
      IntegrableOn (fun r : ℝ ↦ r * g r) (Ioi 0) volume := by
  simpa only [m99A02Point, finrank_euclideanSpace, Fintype.card_fin,
    Nat.reduceSubDiff, pow_one, smul_eq_mul] using
    (MeasureTheory.integrable_fun_norm_addHaar
      (volume : Measure m99A02Point) (f := g))

/-- On the disk, the total squared gradient agrees almost everywhere with
its radial density.  The only omitted point is the null singleton at zero. -/
lemma m99A02_sum_derivative_sq_ae :
    (∀ᵐ x : m99A02Point ∂volume.restrict m99A02Omega,
      ∑ i : Fin 2, (m99A02Derivative i x) ^ 2 =
        1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ))) := by
  have hx0 : ∀ᵐ x : m99A02Point ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae hx0] with x hx hx0
  exact m99A02_sum_derivative_sq hx hx0

/-- The squared function is likewise radial almost everywhere on the disk. -/
lemma m99A02_function_sq_ae :
    (∀ᵐ x : m99A02Point ∂volume.restrict m99A02Omega,
      (m99A02Function x) ^ 2 =
        (-Real.log ‖x‖) ^ (2 / 3 : ℝ)) := by
  have hx0 : ∀ᵐ x : m99A02Point ∂volume, x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae hx0] with x hx hx0
  rw [m99A02Function, if_neg hx0, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (m99A02_neg_log_norm_pos hx hx0).le]
  congr 1
  norm_num

/-- The antiderivative used for the Bertrand density has the required finite
limit at the singular endpoint. -/
lemma m99A02_tendsto_log_antiderivative_zero :
    Tendsto (fun r : ℝ ↦ 3 * (-Real.log r) ^ (-(1 / 3 : ℝ)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hlog : Tendsto (fun r : ℝ ↦ -Real.log r)
      (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have hp : Tendsto (fun u : ℝ ↦ u ^ (-(1 / 3 : ℝ))) atTop (nhds 0) := by
    simpa only using tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  simpa only [mul_zero] using (tendsto_const_nhds.mul (hp.comp hlog))

/-- Interior derivative of the explicit antiderivative for the radial
Bertrand density. -/
lemma m99A02_log_antiderivative_hasDerivAt {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1) :
    HasDerivAt (fun s : ℝ ↦ 3 * (-Real.log s) ^ (-(1 / 3 : ℝ)))
      (1 / (r * (-Real.log r) ^ (4 / 3 : ℝ))) r := by
  have hl : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr0 hr)
  have hpow : HasDerivAt
      (fun s : ℝ ↦ (-Real.log s) ^ (-(1 / 3 : ℝ)))
      (((-(1 / r)) * (-(1 / 3 : ℝ))) *
        (-Real.log r) ^ (-(1 / 3 : ℝ) - 1)) r := by
    simpa only [Pi.neg_apply, one_div] using
      (((Real.hasDerivAt_log hr0.ne').neg).rpow_const
        (p := -(1 / 3 : ℝ)) (Or.inl (ne_of_gt hl)))
  convert (hasDerivAt_const r (3 : ℝ)).mul
    hpow using 1 <;>
    field_simp [hr0.ne', ne_of_gt hl] <;>
    norm_num <;>
    rw [Real.rpow_neg (le_of_lt hl)] <;>
    field_simp [ne_of_gt hl]

/-- Why this unblocks the `MemLp` clauses of `apm_m99a02`: this is the
missing polar-coordinate transport and scalar Bertrand-integral estimate for
the function and both displayed derivatives on the Euclidean disk. -/
theorem apm_m99A02_bridge_1 :
    MemLp m99A02Function 2 (volume.restrict m99A02Omega) ∧
      ∀ i : Fin 2,
        MemLp (m99A02Derivative i) 2 (volume.restrict m99A02Omega) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hfun_bound : ∀ r ∈ Ioo (0 : ℝ) (1 / 2),
      r * (-Real.log r) ^ (2 / 3 : ℝ) ≤ 1 := by
    intro r hr
    have hr1 : r < 1 := hr.2.trans (by norm_num)
    have hl : 0 < -Real.log r := neg_pos.mpr (Real.log_neg hr.1 hr1)
    have hpow : (-Real.log r) ^ (2 / 3 : ℝ) ≤ (-Real.log r) + 1 := by
      by_cases h : -Real.log r ≤ 1
      · calc
          (-Real.log r) ^ (2 / 3 : ℝ) ≤ 1 :=
            Real.rpow_le_one hl.le h (by norm_num)
          _ ≤ -Real.log r + 1 := by linarith
      · have hbase : 1 ≤ -Real.log r := le_of_not_ge h
        calc
          (-Real.log r) ^ (2 / 3 : ℝ) ≤ (-Real.log r) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hbase (by norm_num)
          _ = -Real.log r := by rw [Real.rpow_one]
          _ ≤ -Real.log r + 1 := by linarith
    have hlog : -Real.log r + 1 ≤ 1 / r := by
      rw [show -Real.log r = Real.log (1 / r) by
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hr.1.ne', Real.log_one]
        ring]
      linarith [Real.log_le_sub_one_of_pos (one_div_pos.mpr hr.1)]
    calc
      r * (-Real.log r) ^ (2 / 3 : ℝ) ≤ r * (1 / r) :=
        mul_le_mul_of_nonneg_left (hpow.trans hlog) hr.1.le
      _ = 1 := by simpa [one_div] using mul_inv_cancel₀ hr.1.ne'
  have hfun_scalar : IntegrableOn
      (fun r : ℝ ↦ r * (-Real.log r) ^ (2 / 3 : ℝ)) (Ioo 0 (1 / 2)) volume := by
    apply Integrable.mono' (integrableOn_const (C := (1 : ℝ)) (measure_Ioo_lt_top.ne))
    · fun_prop
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hl : 0 ≤ -Real.log r := (neg_pos.mpr
      (Real.log_neg hr.1 (hr.2.trans (by norm_num)))).le
    have hm : 0 ≤ r * (-Real.log r) ^ (2 / 3 : ℝ) :=
      mul_nonneg hr.1.le (Real.rpow_nonneg hl _)
    rw [Real.norm_eq_abs, abs_of_nonneg hm]
    exact hfun_bound r hr
  have hfun_radial : Integrable
      (fun x : m99A02Point ↦ if ‖x‖ < 1 / 2
        then (-Real.log ‖x‖) ^ (2 / 3 : ℝ) else 0) volume := by
    let g : ℝ → ℝ := fun r ↦ if r < 1 / 2
        then (-Real.log r) ^ (2 / 3 : ℝ) else 0
    change Integrable (fun x : m99A02Point ↦ g ‖x‖) volume
    rw [m99A02_integrable_radial_iff]
    have hi := hfun_scalar.integrable_indicator measurableSet_Ioo
    apply hi.integrableOn.congr_fun
    intro r hr
    have hr0 : 0 < r := hr
    simp [Set.indicator, g, hr0]
    exact measurableSet_Ioi
  have hfun_int : Integrable (fun x ↦ (m99A02Function x) ^ 2)
      (volume.restrict m99A02Omega) := by
    apply hfun_radial.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [m99A02Omega, Metric.mem_ball, dist_zero_right] at hx
    by_cases hx0 : x = 0
    · simp [m99A02Function, hx0]
    · have hxOmega : x ∈ m99A02Omega := by
        simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hx
      rw [m99A02Function, if_neg hx0, ← Real.rpow_natCast,
        ← Real.rpow_mul (m99A02_neg_log_norm_pos hxOmega hx0).le]
      have hx' : ‖x‖ < 2⁻¹ := by simpa only [one_div] using hx
      rw [if_pos hx]
      congr 1
      norm_num
  have hfun_mem : MemLp m99A02Function 2 (volume.restrict m99A02Omega) :=
    (memLp_two_iff_integrable_sq
      (m99A02Function_measurable.aestronglyMeasurable)).2 hfun_int
  refine ⟨hfun_mem, ?_⟩
  intro i
  have hanti_cont : ContinuousOn
      (fun r : ℝ ↦ if r = 0 then 0
        else 3 * (-Real.log r) ^ (-(1 / 3 : ℝ))) (Icc 0 (1 / 2)) := by
    intro r hrI
    by_cases hr : r = 0
    · subst r
      rw [ContinuousWithinAt]
      simp only [if_pos]
      have hset : Icc (0 : ℝ) (1 / 2) = insert 0 (Ioc 0 (1 / 2)) := by
        ext x
        simp
      rw [hset,
        nhdsWithin_insert, Filter.tendsto_sup]
      refine ⟨?_, ?_⟩
      · simpa using (tendsto_pure_nhds
          (fun r : ℝ ↦ if r = 0 then 0 else 3 * (-Real.log r) ^ (-(1 / 3 : ℝ))) 0)
      apply (m99A02_tendsto_log_antiderivative_zero.mono_left
        (nhdsWithin_mono _ Ioc_subset_Ioi_self)).congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp [hx.1.ne']
    · apply ContinuousAt.continuousWithinAt
      have hrpos : 0 < r := lt_of_le_of_ne hrI.1 (Ne.symm hr)
      have hl : -Real.log r ≠ 0 := (neg_pos.mpr
        (Real.log_neg hrpos (hrI.2.trans_lt (by norm_num)))).ne'
      apply ContinuousAt.congr_of_eventuallyEq
        (show ContinuousAt (fun x : ℝ ↦ 3 * (-Real.log x) ^ (-(1 / 3 : ℝ))) r by
          exact continuousAt_const.mul (((Real.continuousAt_log hrpos.ne').neg).rpow_const
            (Or.inl hl)))
      filter_upwards [eventually_ne_nhds hr] with x hx
      simp [hx]
  have hder_scalar0 : IntegrableOn
      (fun r : ℝ ↦ 1 / (r * (-Real.log r) ^ (4 / 3 : ℝ)))
      (Ioo 0 (1 / 2)) volume := by
    rw [← integrableOn_Ioc_iff_integrableOn_Ioo]
    apply intervalIntegral.integrableOn_deriv_of_nonneg hanti_cont
    · intro r hr
      apply HasDerivAt.congr_of_eventuallyEq
        (m99A02_log_antiderivative_hasDerivAt hr.1
          (hr.2.trans (by norm_num)))
      filter_upwards [eventually_ne_nhds hr.1.ne'] with x hx
      simp [hx]
    · intro r hr
      have hl : 0 < -Real.log r := neg_pos.mpr
        (Real.log_neg hr.1 (hr.2.trans (by norm_num)))
      exact one_div_nonneg.mpr (mul_nonneg hr.1.le (Real.rpow_nonneg hl.le _))
  have hder_scalar : IntegrableOn
      (fun r : ℝ ↦ 1 / (9 * r * (-Real.log r) ^ (4 / 3 : ℝ)))
      (Ioo 0 (1 / 2)) volume := by
    apply (hder_scalar0.const_mul (1 / 9 : ℝ)).congr
    filter_upwards with r
    ring
  have hgrad_radial : Integrable
      (fun x : m99A02Point ↦ if ‖x‖ < 1 / 2
        then 1 / (9 * ‖x‖ ^ 2 * (-Real.log ‖x‖) ^ (4 / 3 : ℝ)) else 0) volume := by
    let g : ℝ → ℝ := fun r ↦ if r < 1 / 2
        then 1 / (9 * r ^ 2 * (-Real.log r) ^ (4 / 3 : ℝ)) else 0
    change Integrable (fun x : m99A02Point ↦ g ‖x‖) volume
    rw [m99A02_integrable_radial_iff]
    have hi := hder_scalar.integrable_indicator measurableSet_Ioo
    apply hi.integrableOn.congr_fun
    intro r hr
    simp only [Set.indicator, mem_Ioo, g]
    have hr0 : 0 < r := hr
    by_cases h : r < 1 / 2
    · simp [h, hr0]
      field_simp
    · have hn : ¬(0 < r ∧ r < 1 / 2) := fun hh ↦ h hh.2
      have h' : ¬ r < 2⁻¹ := by simpa only [one_div] using h
      have hle : 2⁻¹ ≤ r := by
        rw [show (2⁻¹ : ℝ) = 1 / 2 by norm_num]
        exact le_of_not_gt h
      simp [h, hn, h']
    exact measurableSet_Ioi
  have hgrad_int : Integrable
      (fun x ↦ ∑ j : Fin 2, (m99A02Derivative j x) ^ 2)
      (volume.restrict m99A02Omega) := by
    apply hgrad_radial.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    simp only [m99A02Omega, Metric.mem_ball, dist_zero_right] at hx
    by_cases hx0 : x = 0
    · simp [m99A02Derivative, hx0]
    · change (if ‖x‖ < 1 / 2 then _ else _) = ∑ j, _
      have hxOmega : x ∈ m99A02Omega := by
        simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hx
      rw [m99A02_sum_derivative_sq hxOmega hx0]
      have hx' : ‖x‖ < 2⁻¹ := by simpa only [one_div] using hx
      rw [if_pos hx]
  apply (memLp_two_iff_integrable_sq
    ((m99A02Derivative_measurable i).aestronglyMeasurable)).2
  apply hgrad_int.mono'
  · exact ((m99A02Derivative_measurable i).pow_const 2).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (m99A02Derivative j x))
    (Finset.mem_univ i)

/-! ### Split of `apm_m99A02_bridge_2` (claude-14, 2026-10-13, after a partial round-1 attempt)

Route: integrate along lines parallel to `eᵢ` at height `c ≠ 0` in the other coordinate.
Such lines miss the singularity, so 1-D integration by parts applies; Fubini and the
null line `c = 0` give the planar identity. Each lemma takes what it needs from the
others as hypotheses, so all five can be proved at the same time. -/

/-- The other coordinate index in `Fin 2`. -/
def m99A02Other (i : Fin 2) : Fin 2 := Equiv.swap (0 : Fin 2) 1 i

/-- The line `t ↦ t eᵢ + c eⱼ`, `j ≠ i`. -/
noncomputable def m99A02Line (i : Fin 2) (c t : ℝ) : m99A02Point :=
  EuclideanSpace.single i t + EuclideanSpace.single (m99A02Other i) c

/-- Away from the origin and inside the unit disk, `f` is differentiable along
`eᵢ` with derivative the displayed `m99A02Derivative i`. -/
theorem apm_m99A02_directional_hasDerivAt (i : Fin 2) (x : m99A02Point)
    (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) :
    HasDerivAt (fun t : ℝ ↦ m99A02Function (x + t • EuclideanSpace.single i 1))
      (m99A02Derivative i x) 0 := by
  sorry

/-- One-dimensional integration by parts on a line that misses the origin. -/
theorem apm_m99A02_line_ibp (i : Fin 2) {c : ℝ} (hc : c ≠ 0)
    (hdir : ∀ x : m99A02Point, x ≠ 0 → ‖x‖ < 1 →
      HasDerivAt (fun t : ℝ ↦ m99A02Function (x + t • EuclideanSpace.single i 1))
        (m99A02Derivative i x) 0)
    (φ : m99A02Point → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : Function.support φ ⊆ m99A02Omega) :
    (∫ t : ℝ, m99A02Function (m99A02Line i c t) *
        fderiv ℝ φ (m99A02Line i c t) (EuclideanSpace.single i 1)) =
      -∫ t : ℝ, m99A02Derivative i (m99A02Line i c t) * φ (m99A02Line i c t) := by
  sorry

/-- Fubini in the coordinates `(t, c)` of `m99A02Line i c t`. -/
theorem apm_m99A02_integral_eq_iterated (i : Fin 2) (F : m99A02Point → ℝ)
    (hF : Integrable F) :
    (∫ x, F x) = ∫ c : ℝ, ∫ t : ℝ, F (m99A02Line i c t) := by
  sorry

/-- Both integrands are integrable on `Ω` (use `apm_m99A02_bridge_1`: `L²` on a
finite-measure set is `L¹`, and `φ`, `Dφ` are bounded). -/
-- BEGIN SEAT AREA
theorem apm_m99A02_weak_integrands_integrable (i : Fin 2)
    (φ : m99A02Point → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ m99A02Function x * fderiv ℝ φ x (EuclideanSpace.single i 1))
        (volume.restrict m99A02Omega) ∧
      Integrable (fun x ↦ m99A02Derivative i x * φ x) (volume.restrict m99A02Omega) := by
  let e : m99A02Point := EuclideanSpace.single i 1
  have hDcont : Continuous (fun x ↦ fderiv ℝ φ x e) := by
    have hfderiv : Continuous (fderiv ℝ φ) :=
      hφ.continuous_fderiv (by simp)
    fun_prop
  have hDcompact : HasCompactSupport (fun x ↦ fderiv ℝ φ x e) :=
    hφc.fderiv_apply ℝ e
  have hDtwo : MemLp (fun x ↦ fderiv ℝ φ x e) 2
      (volume.restrict m99A02Omega) :=
    hDcont.memLp_of_hasCompactSupport hDcompact
  have hφtwo : MemLp φ 2 (volume.restrict m99A02Omega) :=
    hφ.continuous.memLp_of_hasCompactSupport hφc
  constructor
  · simpa only [e, Pi.mul_apply] using
      apm_m99A02_bridge_1.1.integrable_mul hDtwo
  · simpa only [Pi.mul_apply] using
      (apm_m99A02_bridge_1.2 i).integrable_mul hφtwo
-- END SEAT AREA

/-- Assembly from the pieces: pass from `Ω` to the whole plane (`tsupport φ` lies in
the closed disk, whose boundary circle is null), apply Fubini, and use the line
identity for every `c ≠ 0` (the line `c = 0` is a null set of heights). -/
theorem apm_m99A02_weak_identity_of_pieces (i : Fin 2)
    (φ : m99A02Point → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : Function.support φ ⊆ m99A02Omega)
    (hline : ∀ c : ℝ, c ≠ 0 →
      (∫ t : ℝ, m99A02Function (m99A02Line i c t) *
          fderiv ℝ φ (m99A02Line i c t) (EuclideanSpace.single i 1)) =
        -∫ t : ℝ, m99A02Derivative i (m99A02Line i c t) * φ (m99A02Line i c t))
    (hfub : ∀ F : m99A02Point → ℝ, Integrable F →
      (∫ x, F x) = ∫ c : ℝ, ∫ t : ℝ, F (m99A02Line i c t))
    (hint : Integrable (fun x ↦ m99A02Function x * fderiv ℝ φ x (EuclideanSpace.single i 1))
        (volume.restrict m99A02Omega) ∧
      Integrable (fun x ↦ m99A02Derivative i x * φ x) (volume.restrict m99A02Omega)) :
    (∫ x in m99A02Omega, m99A02Function x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      -∫ x in m99A02Omega, m99A02Derivative i x * φ x := by
  sorry

/-- Why this unblocks the weak-derivative clauses of `apm_m99a02`: this is
the punctured-disk integration-by-parts theorem together with the assertion
that the inner-circle boundary flux tends to zero at the logarithmic
singularity. -/
theorem apm_m99A02_bridge_2 (i : Fin 2) :
    IsM99A02WeakDerivative m99A02Function (m99A02Derivative i) i := by
  intro φ hφ hφc hφΩ
  exact apm_m99A02_weak_identity_of_pieces i φ hφ hφc hφΩ
    (fun c hc ↦ apm_m99A02_line_ibp i hc
      (fun x hx0 hx1 ↦ apm_m99A02_directional_hasDerivAt i x hx0 hx1) φ hφ hφc hφΩ)
    (apm_m99A02_integral_eq_iterated i)
    (apm_m99A02_weak_integrands_integrable i φ hφ hφc)

theorem apm_m99a02 :
    MemLp m99A02Function 2 (volume.restrict m99A02Omega) ∧
    ∀ i : Fin 2,
      MemLp (m99A02Derivative i) 2 (volume.restrict m99A02Omega) ∧
      IsM99A02WeakDerivative m99A02Function (m99A02Derivative i) i := by
  refine ⟨apm_m99A02_bridge_1.1, ?_⟩
  intro i
  exact ⟨apm_m99A02_bridge_1.2 i, apm_m99A02_bridge_2 i⟩


#print axioms apm_m99a02
