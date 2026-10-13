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
  let e : m99A02Point := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have hv : HasDerivAt (fun t : ℝ ↦ x + t • e) e 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) x).add
      ((hasDerivAt_id (0 : ℝ)).smul_const e) using 1 <;> simp
  have hq := hv.hasFDerivAt.norm_sq.hasDerivAt
  have hq' : HasDerivAt (fun t : ℝ ↦ ‖x + t • e‖ ^ 2) (2 * x i) 0 := by
    convert hq using 1
    simp only [zero_smul, add_zero, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      one_smul, smul_eq_mul]
    simp only [e, innerSL_apply]
    simp [PiLp.inner_apply, EuclideanSpace.single_apply]
    fin_cases i <;> simp <;> erw [RCLike.inner_apply] <;> simp
  have hnorm : HasDerivAt (fun t : ℝ ↦ ‖x + t • e‖) (x i / ‖x‖) 0 := by
    have hn2 : ‖x + (0 : ℝ) • e‖ ^ 2 ≠ 0 := by
      simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0)
    have hs := (Real.hasDerivAt_sqrt hn2).comp 0 hq'
    convert hs using 1
    · funext t
      simp [Function.comp_def, Real.sqrt_sq_eq_abs]
    · simp only [zero_smul, add_zero, Real.sqrt_sq_eq_abs, abs_norm]
      field_simp [norm_ne_zero_iff.mpr hx0]
  have hlog : HasDerivAt (fun t : ℝ ↦ -Real.log ‖x + t • e‖)
      (-(x i) / ‖x‖ ^ 2) 0 := by
    have hn0 : ‖x + (0 : ℝ) • e‖ ≠ 0 := by
      simpa using norm_ne_zero_iff.mpr hx0
    have hlog0 := Real.hasDerivAt_log hn0
    have hc := hlog0.comp 0 hnorm
    simp only [zero_smul, add_zero] at hc
    convert hc.neg using 1
    field_simp [norm_ne_zero_iff.mpr hx0]
  have hl : 0 < -Real.log ‖x‖ := neg_pos.mpr
    (Real.log_neg (norm_pos_iff.mpr hx0) hx1)
  have hl0 : -Real.log ‖x + (0 : ℝ) • e‖ ≠ 0 := by simpa using hl.ne'
  have hpow0 := Real.hasDerivAt_rpow_const
    (p := (1 / 3 : ℝ)) (Or.inl hl0)
  have hp := hpow0.comp 0 hlog
  simp only [zero_smul, add_zero] at hp
  rw [m99A02Derivative, if_neg hx0]
  change HasDerivAt (fun t : ℝ ↦
    (if x + t • EuclideanSpace.single i 1 = 0 then 0
      else (-Real.log ‖x + t • EuclideanSpace.single i 1‖) ^ (1 / 3 : ℝ))) _ 0
  have hxbase : x + (0 : ℝ) • e ≠ 0 := by simpa using hx0
  have hev := hv.continuousAt.eventually_ne (y := 0) hxbase
  have heq : (fun t : ℝ ↦
      (if x + t • EuclideanSpace.single i 1 = 0 then 0
        else (-Real.log ‖x + t • EuclideanSpace.single i 1‖) ^ (1 / 3 : ℝ))) =ᶠ[nhds 0]
      ((fun u : ℝ ↦ u ^ (1 / 3 : ℝ)) ∘ fun t ↦ -Real.log ‖x + t • e‖) := by
    filter_upwards [hev] with t ht
    simp [e, ht, Function.comp_def]
  convert (hp.congr_of_eventuallyEq heq) using 1
  · field_simp [norm_ne_zero_iff.mpr hx0, hl.ne']
    rw [show ((1 - 3 : ℝ) / 3) = -(2 / 3 : ℝ) by norm_num,
      Real.rpow_neg hl.le]
    field_simp [hl.ne']

/-- One-dimensional integration by parts on a line that misses the origin. -/
lemma apm_m99A02_line_ibp_aux_option_anchor : True := by trivial
set_option maxHeartbeats 3000000
theorem apm_m99A02_line_ibp (i : Fin 2) {c : ℝ} (hc : c ≠ 0)
    (hdir : ∀ x : m99A02Point, x ≠ 0 → ‖x‖ < 1 →
      HasDerivAt (fun t : ℝ ↦ m99A02Function (x + t • EuclideanSpace.single i 1))
        (m99A02Derivative i x) 0)
    (φ : m99A02Point → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : Function.support φ ⊆ m99A02Omega) :
    (∫ t : ℝ, m99A02Function (m99A02Line i c t) *
        fderiv ℝ φ (m99A02Line i c t) (EuclideanSpace.single i 1)) =
      -∫ t : ℝ, m99A02Derivative i (m99A02Line i c t) * φ (m99A02Line i c t) := by
  let L : ℝ → m99A02Point := fun t ↦ m99A02Line i c t
  let u : ℝ → ℝ := fun t ↦ m99A02Function (L t)
  let v : ℝ → ℝ := fun t ↦ φ (L t)
  let u' : ℝ → ℝ := fun t ↦ m99A02Derivative i (L t)
  let v' : ℝ → ℝ := fun t ↦ fderiv ℝ φ (L t) (EuclideanSpace.single i 1)
  have hother : m99A02Other i ≠ i := by
    fin_cases i <;> simp [m99A02Other]
  have hLi (t : ℝ) : L t i = t := by
    simp [L, m99A02Line, hother]
  have hLo (t : ℝ) : L t (m99A02Other i) = c := by
    have hoi : i ≠ m99A02Other i := Ne.symm hother
    simp [L, m99A02Line, hoi]
  have hL0 (t : ℝ) : L t ≠ 0 := by
    intro h
    have this := hLo t
    rw [h] at this
    simp only [PiLp.zero_apply] at this
    exact hc this.symm
  have hLder (t : ℝ) : HasDerivAt L (EuclideanSpace.single i 1) t := by
    have hsmul (s : ℝ) : s • EuclideanSpace.single i 1 = EuclideanSpace.single i s := by
      ext j
      simp [EuclideanSpace.single_apply, mul_boole]
    dsimp [L, m99A02Line]
    simpa only [one_smul, hsmul] using
      ((hasDerivAt_id t).smul_const (EuclideanSpace.single i 1)).add_const
        (EuclideanSpace.single (m99A02Other i) c)
  have hLcont : Continuous L := continuous_iff_continuousAt.2 fun t ↦ (hLder t).continuousAt
  have hv_deriv (t : ℝ) : HasDerivAt v (v' t) t := by
    dsimp [v, v']
    simpa only [one_smul] using
      (hφ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t (hLder t)
  have hv_comp : HasCompactSupport v := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))
    intro t ht
    apply Classical.byContradiction
    intro hn
    have hs : L t ∈ Function.support φ := hn
    have hom := hφΩ hs
    have hnorm : ‖L t‖ < 1 / 2 := by
      simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hom
    have hcoord : |t| ≤ ‖L t‖ := by
      calc
        |t| = ‖(L t) i‖ := by rw [hLi]; exact (Real.norm_eq_abs t).symm
        _ ≤ ‖L t‖ := PiLp.norm_apply_le (L t) i
    have : |t| < 1 := hcoord.trans_lt (hnorm.trans (by norm_num))
    exact ht ⟨(abs_lt.mp this).1.le, (abs_lt.mp this).2.le⟩
  have hu_deriv (t : ℝ) (ht : t ∈ tsupport v) : HasDerivAt u (u' t) t := by
    have hsupp : Function.support v ⊆ L ⁻¹' Metric.closedBall 0 (1 / 2) := by
      intro s hs
      have hom := hφΩ hs
      have : ‖L s‖ < 1 / 2 := by
        simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hom
      simpa [Metric.mem_closedBall, dist_zero_right] using this.le
    have hs' : t ∈ L ⁻¹' Metric.closedBall 0 (1 / 2) :=
      (closure_minimal hsupp (Metric.isClosed_closedBall.preimage hLcont)) ht
    have hn : ‖L t‖ ≤ 1 / 2 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hs'
    have hd := hdir (L t) (hL0 t) (hn.trans_lt (by norm_num))
    have htrans : (fun s : ℝ ↦ L t + (s - t) • EuclideanSpace.single i 1) = L := by
      funext s
      ext j
      fin_cases i <;> fin_cases j <;>
        simp [L, m99A02Line, m99A02Other] <;> ring
    have hd0 : HasDerivAt
        (fun q ↦ m99A02Function (L t + q • EuclideanSpace.single i 1))
        (m99A02Derivative i (L t)) (t - t) := by simpa using hd
    have hcomp := hd0.comp_sub_const t t
    have hftrans :
        (fun s ↦ m99A02Function (L t + (s - t) • EuclideanSpace.single i 1)) = u := by
      simpa only [u, Function.comp_apply] using
        congrArg (fun F ↦ m99A02Function ∘ F) htrans
    rw [hftrans] at hcomp
    exact hcomp
  have hu_cont : Continuous u := by
    have heq : u = fun t ↦ (-Real.log ‖L t‖) ^ (1 / 3 : ℝ) := by
      funext t
      simp [u, m99A02Function, hL0]
    rw [heq]
    have hlog : Continuous (fun t ↦ -Real.log ‖L t‖) :=
      ((continuous_norm.comp hLcont).log
        (fun t ↦ (norm_pos_iff.mpr (hL0 t)).ne')).neg
    exact (Real.continuous_rpow_const (by norm_num)).comp hlog
  have hv_cont : Continuous v :=
    continuous_iff_continuousAt.2 fun t ↦ (hv_deriv t).continuousAt
  have hv'_cont : Continuous v' := by
    dsimp [v']
    exact (hφ.continuous_fderiv_apply (by simp)).comp
      (Continuous.prodMk hLcont continuous_const)
  have hu'v_cont : Continuous (u' * v) := by
    rw [continuous_iff_continuousAt]
    intro t
    by_cases ht : t ∈ tsupport v
    · have hsupp : Function.support v ⊆ L ⁻¹' Metric.closedBall 0 (1 / 2) := by
        intro s hs
        have hom := hφΩ hs
        have hh : ‖L s‖ < 1 / 2 := by
          simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hom
        simpa [Metric.mem_closedBall, dist_zero_right] using hh.le
      have hs' : t ∈ L ⁻¹' Metric.closedBall 0 (1 / 2) :=
        (closure_minimal hsupp (Metric.isClosed_closedBall.preimage hLcont)) ht
      have hn : ‖L t‖ < 1 := by
        have : ‖L t‖ ≤ 1 / 2 := by
          simpa [Metric.mem_closedBall, dist_zero_right] using hs'
        exact this.trans_lt (by norm_num)
      apply ContinuousAt.mul _ hv_cont.continuousAt
      dsimp [u', m99A02Derivative]
      simp only [hL0, ↓reduceIte]
      have hp : 0 < -Real.log ‖L t‖ :=
        neg_pos.mpr (Real.log_neg (norm_pos_iff.mpr (hL0 t)) hn)
      have hcL : Continuous (fun s ↦ (L s) i) := by
        convert continuous_id using 1
        funext s
        exact hLi s
      have hnorm : Continuous (fun s ↦ ‖L s‖) := continuous_norm.comp hLcont
      have hlog : Continuous (fun s ↦ -Real.log ‖L s‖) :=
        ((continuous_norm.comp hLcont).log
          (fun s ↦ (norm_pos_iff.mpr (hL0 s)).ne')).neg
      apply ContinuousAt.div₀ (hcL.neg.continuousAt)
        ((continuous_const.mul (hnorm.pow 2)).mul
          ((Real.continuous_rpow_const (by norm_num)).comp hlog)).continuousAt
      exact mul_ne_zero (mul_ne_zero (by norm_num)
        (pow_ne_zero _ (norm_pos_iff.mpr (hL0 t)).ne'))
        (Real.rpow_pos_of_pos hp _).ne'
    · have hz : ∀ᶠ s in nhds t, v s = 0 := by
        filter_upwards [(isClosed_tsupport (f := v)).isOpen_compl.mem_nhds ht] with s hs
        exact not_ne_iff.mp (fun h ↦ hs (subset_closure h))
      have heq : (u' * v) =ᶠ[nhds t] fun _ ↦ 0 := by
        filter_upwards [hz] with s hs
        simp [hs]
      exact continuousAt_const.congr_of_eventuallyEq heq
  have huv'_int : Integrable (u * v') :=
    (hu_cont.mul hv'_cont).integrable_of_hasCompactSupport (by
      have hv'eq : v' = deriv v := by
        funext t
        exact (hv_deriv t).deriv.symm
      rw [hv'eq]
      exact hv_comp.deriv.mul_left)
  have hu'v_int : Integrable (u' * v) :=
    hu'v_cont.integrable_of_hasCompactSupport hv_comp.mul_left
  have huv_int : Integrable (u * v) :=
    (hu_cont.mul hv_cont).integrable_of_hasCompactSupport hv_comp.mul_left
  simpa [u, v, u', v', L] using
    integral_mul_deriv_eq_deriv_mul_of_integrable hu_deriv
      (fun t _ ↦ hv_deriv t) huv'_int hu'v_int huv_int

/-- Fubini in the coordinates `(t, c)` of `m99A02Line i c t`. -/
theorem apm_m99A02_integral_eq_iterated (i : Fin 2) (F : m99A02Point → ℝ)
    (hF : Integrable F) :
    (∫ x, F x) = ∫ c : ℝ, ∫ t : ℝ, F (m99A02Line i c t) := by
  let e : ℝ × ℝ ≃ᵐ m99A02Point :=
    (MeasurableEquiv.finTwoArrow.symm.trans
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)))
  have he : MeasurePreserving e volume volume :=
    ((PiLp.volume_preserving_ofLp (Fin 2)).symm
      (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm).comp
      ((volume_preserving_finTwoArrow ℝ).symm MeasurableEquiv.finTwoArrow)
  have hcomp : Integrable (fun z : ℝ × ℝ ↦ F (e z)) :=
    he.integrable_comp_of_integrable hF
  fin_cases i
  · calc
      (∫ x, F x) = ∫ z : ℝ × ℝ, F (e z) :=
        (he.integral_comp e.measurableEmbedding F).symm
      _ = ∫ c : ℝ, ∫ t : ℝ, F (e (t, c)) := integral_prod_symm _ hcomp
      _ = ∫ c : ℝ, ∫ t : ℝ, F (m99A02Line 0 c t) := by
        congr 1
        funext c
        congr 1
        funext t
        apply congrArg F
        ext j
        fin_cases j <;> simp [e, m99A02Line, m99A02Other]
  · calc
      (∫ x, F x) = ∫ z : ℝ × ℝ, F (e z) :=
        (he.integral_comp e.measurableEmbedding F).symm
      _ = ∫ c : ℝ, ∫ t : ℝ, F (e (c, t)) := integral_prod _ hcomp
      _ = ∫ c : ℝ, ∫ t : ℝ, F (m99A02Line 1 c t) := by
        congr 1
        funext c
        congr 1
        funext t
        apply congrArg F
        ext j
        fin_cases j <;> simp [e, m99A02Line, m99A02Other]

/-- Both integrands are integrable on `Ω` (use `apm_m99A02_bridge_1`: `L²` on a
finite-measure set is `L¹`, and `φ`, `Dφ` are bounded). -/
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
  let A : m99A02Point → ℝ := fun x ↦
    m99A02Function x * fderiv ℝ φ x (EuclideanSpace.single i 1)
  let B : m99A02Point → ℝ := fun x ↦ m99A02Derivative i x * φ x
  have hzero : ∀ x : m99A02Point, 1 / 2 < ‖x‖ → φ x = 0 ∧
      fderiv ℝ φ x (EuclideanSpace.single i 1) = 0 := by
    intro x hx
    have hxC : x ∈ (Metric.closedBall (0 : m99A02Point) (1 / 2))ᶜ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    have hevC : ∀ᶠ y in nhds x,
        y ∈ (Metric.closedBall (0 : m99A02Point) (1 / 2))ᶜ :=
      (Metric.isClosed_closedBall.isOpen_compl.mem_nhds hxC)
    have hev : φ =ᶠ[nhds x] (fun _ ↦ 0) := by
      filter_upwards [hevC] with y hy
      by_contra hy0
      have hys : y ∈ Function.support φ := hy0
      have hyΩ := hφΩ hys
      have : ‖y‖ < 1 / 2 := by
        simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hyΩ
      exact hy (by simpa [Metric.mem_closedBall, dist_zero_right] using this.le)
    constructor
    · exact hev.self_of_nhds
    · rw [hev.fderiv_eq]
      simp
  have hae : ∀ᵐ x : m99A02Point ∂volume,
      A x = m99A02Omega.indicator A x ∧ B x = m99A02Omega.indicator B x := by
    have hs : volume (Metric.sphere (0 : m99A02Point) (1 / 2)) = 0 :=
      Measure.addHaar_sphere volume 0 (1 / 2)
    have haeS : ∀ᵐ x : m99A02Point ∂volume,
        x ∉ Metric.sphere 0 (1 / 2) := by
      rw [ae_iff]
      simpa only [not_not, setOf_mem_eq] using hs
    filter_upwards [haeS] with x hxS
    by_cases hx : ‖x‖ < 1 / 2
    · have hxΩ : x ∈ m99A02Omega := by
        simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hx
      simp [Set.indicator_of_mem hxΩ]
    · have hne : ‖x‖ ≠ 1 / 2 := by
        intro heq
        apply hxS
        simpa [Metric.mem_sphere, dist_zero_right] using heq
      have hgt : 1 / 2 < ‖x‖ := lt_of_le_of_ne (le_of_not_gt hx) (Ne.symm hne)
      have hz := hzero x hgt
      have hxΩ : x ∉ m99A02Omega := by
        intro hxmem
        have hlt : ‖x‖ < 1 / 2 := by
          simpa [m99A02Omega, Metric.mem_ball, dist_zero_right] using hxmem
        exact (not_lt_of_ge hgt.le) hlt
      simp [A, B, Set.indicator, hxΩ, hz.1, hz.2]
  have hAi : Integrable (m99A02Omega.indicator A) :=
    IntegrableOn.integrable_indicator hint.1 measurableSet_ball
  have hBi : Integrable (m99A02Omega.indicator B) :=
    IntegrableOn.integrable_indicator hint.2 measurableSet_ball
  have hA : Integrable A := hAi.congr (hae.mono fun _ h ↦ h.1.symm)
  have hB : Integrable B := hBi.congr (hae.mono fun _ h ↦ h.2.symm)
  have hline_ae : ∀ᵐ c : ℝ ∂volume,
      (∫ t : ℝ, A (m99A02Line i c t)) =
        -∫ t : ℝ, B (m99A02Line i c t) := by
    filter_upwards [show ∀ᵐ c : ℝ ∂volume, c ≠ 0 by
      rw [ae_iff]; simp] with c hc
    exact hline c hc
  calc
    (∫ x in m99A02Omega, m99A02Function x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x, A x := by
      change (∫ x in m99A02Omega, A x) = ∫ x, A x
      rw [← integral_indicator (s := m99A02Omega) measurableSet_ball]
      exact integral_congr_ae (hae.mono fun _ h ↦ h.1.symm)
    _ = ∫ c : ℝ, ∫ t : ℝ, A (m99A02Line i c t) := hfub A hA
    _ = ∫ c : ℝ, -(∫ t : ℝ, B (m99A02Line i c t)) :=
      integral_congr_ae hline_ae
    _ = -(∫ c : ℝ, ∫ t : ℝ, B (m99A02Line i c t)) := by rw [integral_neg]
    _ = -(∫ x, B x) := by rw [hfub B hB]
    _ = -∫ x in m99A02Omega, m99A02Derivative i x * φ x := by
      congr 1
      change (∫ x, B x) = ∫ x in m99A02Omega, B x
      rw [← integral_indicator (s := m99A02Omega) measurableSet_ball]
      exact integral_congr_ae (hae.mono fun _ h ↦ h.2)

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
