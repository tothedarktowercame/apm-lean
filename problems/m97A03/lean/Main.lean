import Mathlib

/-!
# APM m97A03: A nonlinear integral equation

## Statement repairs

None.

## Encoding questions

None. The singular kernel is encoded exactly in a Lebesgue integral on
`[0,1]`. Its convention-dependent value at the single endpoint `s = 0` does
not affect the integral.
-/

open MeasureTheory Set

noncomputable section

def apm_m97A03_isSolution (lam : ℝ) (u : ℝ → ℝ) : Prop :=
  ContinuousOn u (Icc 0 1) ∧
  ∀ t ∈ Icc (0 : ℝ) 1,
    u t - lam * (∫ s in Icc (0 : ℝ) 1,
      Real.sqrt ((t + 3) / s) * Real.sin (t * u s)) = Real.exp t

lemma apm_m97A03_t_sqrt_bound {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ t * Real.sqrt (t + 3) ∧ t * Real.sqrt (t + 3) ≤ 2 := by
  have ht3 : 0 ≤ t + 3 := by linarith [ht.1]
  have hs0 : 0 ≤ Real.sqrt (t + 3) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (t + 3) ≤ 2 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith [ht.2]⟩
  constructor
  · exact mul_nonneg ht.1 hs0
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) hs0]

/-- The endpoint singularity used to dominate the Hammerstein kernel is
integrable, with its sharp elementary integral. -/
lemma apm_m97A03_integral_rpow_neg_half :
    (∫ s in Icc (0 : ℝ) 1, s ^ (-1 / 2 : ℝ)) = 2 := by
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by norm_num))]
  norm_num

/-- The singular majorant is integrable on the closed interval; changing the
two endpoints from the standard open-interval theorem is measure-theoretically
harmless. -/
lemma apm_m97A03_integrableOn_rpow_neg_half :
    IntegrableOn (fun s : ℝ ↦ s ^ (-1 / 2 : ℝ)) (Icc 0 1) := by
  refine IntegrableOn.congr_set_ae
    ((intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1)).2 (by norm_num)) ?_
  exact (Ioo_ae_eq_Icc : Ioo (0 : ℝ) 1 =ᵐ[volume] Icc 0 1).symm

/-- Away from the null endpoint, the singular square-root kernel factors into
its parameter part and the integrable power majorant. -/
lemma apm_m97A03_sqrt_div_factor {t s : ℝ} (ht : 0 ≤ t + 3) (hs : 0 < s) :
    Real.sqrt ((t + 3) / s) =
      Real.sqrt (t + 3) * s ^ (-1 / 2 : ℝ) := by
  rw [Real.sqrt_div ht]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hs.le]
  rfl

/-- The factor in the Lipschitz estimate is pointwise dominated by the sharp
integrable majorant on the punctured interval. -/
lemma apm_m97A03_kernel_lipschitz_majorant {t s : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 < s) :
    t * Real.sqrt ((t + 3) / s) ≤ 2 * s ^ (-1 / 2 : ℝ) := by
  rw [apm_m97A03_sqrt_div_factor (by linarith [ht.1]) hs]
  have hpow : 0 ≤ s ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hs.le _
  calc
    t * (Real.sqrt (t + 3) * s ^ (-1 / 2 : ℝ)) =
        (t * Real.sqrt (t + 3)) * s ^ (-1 / 2 : ℝ) := by ring
    _ ≤ 2 * s ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right (apm_m97A03_t_sqrt_bound ht).2 hpow

/-- Pointwise Lipschitz domination for the nonlinear singular integrand. -/
lemma apm_m97A03_integrand_sub_bound {t s u v : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 < s) :
    |Real.sqrt ((t + 3) / s) * (Real.sin (t * u) - Real.sin (t * v))| ≤
      2 * s ^ (-1 / 2 : ℝ) * |u - v| := by
  have hk0 : 0 ≤ Real.sqrt ((t + 3) / s) := Real.sqrt_nonneg _
  have hsin := Real.abs_sin_sub_sin_le (t * u) (t * v)
  have huv0 : 0 ≤ |u - v| := abs_nonneg _
  calc
    |Real.sqrt ((t + 3) / s) * (Real.sin (t * u) - Real.sin (t * v))| =
        Real.sqrt ((t + 3) / s) * |Real.sin (t * u) - Real.sin (t * v)| := by
          rw [abs_mul, abs_of_nonneg hk0]
    _ ≤ Real.sqrt ((t + 3) / s) * |t * u - t * v| :=
      mul_le_mul_of_nonneg_left hsin hk0
    _ = (t * Real.sqrt ((t + 3) / s)) * |u - v| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg ht.1]
      ring
    _ ≤ (2 * s ^ (-1 / 2 : ℝ)) * |u - v| :=
      mul_le_mul_of_nonneg_right (apm_m97A03_kernel_lipschitz_majorant ht hs) huv0

/-- Integrated form of the contraction estimate. The auxiliary uniform bound
`B` is what will later be instantiated by the `ContinuousMap` sup norm. -/
lemma apm_m97A03_integral_integrand_sub_bound
    {t B : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (u v : ℝ → ℝ) (huv : ∀ s ∈ Icc (0 : ℝ) 1, |u s - v s| ≤ B) :
    |∫ s in Icc (0 : ℝ) 1,
        Real.sqrt ((t + 3) / s) *
          (Real.sin (t * u s) - Real.sin (t * v s))| ≤ 4 * B := by
  have hg : IntegrableOn (fun s : ℝ ↦ 2 * s ^ (-1 / 2 : ℝ) * B) (Icc 0 1) :=
    (apm_m97A03_integrableOn_rpow_neg_half.const_mul 2).mul_const B
  have hae : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      ‖Real.sqrt ((t + 3) / s) *
          (Real.sin (t * u s) - Real.sin (t * v s))‖ ≤
        2 * s ^ (-1 / 2 : ℝ) * B := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    by_cases hs0 : s = 0
    · simp [hs0]
    · exact (apm_m97A03_integrand_sub_bound ht (lt_of_le_of_ne hs.1 (Ne.symm hs0)) |>.trans
        (mul_le_mul_of_nonneg_left (huv s hs) (mul_nonneg (by norm_num)
          (Real.rpow_nonneg hs.1 _))))
  calc
    |∫ s in Icc (0 : ℝ) 1, Real.sqrt ((t + 3) / s) *
        (Real.sin (t * u s) - Real.sin (t * v s))| ≤
        ∫ s in Icc (0 : ℝ) 1, 2 * s ^ (-1 / 2 : ℝ) * B :=
      norm_integral_le_of_norm_le hg hae
    _ = 4 * B := by rw [integral_mul_const, integral_const_mul,
      apm_m97A03_integral_rpow_neg_half]; ring

lemma apm_m97A03_integrand_bound {t s z : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hs : 0 < s) :
    |Real.sqrt ((t + 3) / s) * Real.sin (t * z)| ≤
      2 * s ^ (-1 / 2 : ℝ) := by
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hsqrt : Real.sqrt (t + 3) ≤ 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith [ht.1, ht.2]
  have hpow := Real.rpow_nonneg hs.le (-1 / 2 : ℝ)
  rw [apm_m97A03_sqrt_div_factor (by linarith [ht.1]) hs]
  calc
    Real.sqrt (t + 3) * s ^ (-1 / 2 : ℝ) * |Real.sin (t * z)| ≤
        Real.sqrt (t + 3) * s ^ (-1 / 2 : ℝ) := by
      have hsin := Real.abs_sin_le_one (t * z)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hsin
        (mul_nonneg (Real.sqrt_nonneg (t + 3)) hpow)
    _ ≤ 2 * s ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right hsqrt hpow

lemma apm_m97A03_integral_continuousOn (u : ℝ → ℝ)
    (hu : ContinuousOn u (Icc 0 1)) :
    ContinuousOn (fun t ↦ ∫ s in Icc (0 : ℝ) 1,
      Real.sqrt ((t + 3) / s) * Real.sin (t * u s)) (Icc 0 1) := by
  let F : ℝ → ℝ → ℝ := fun t s ↦
    Real.sqrt ((t + 3) / s) * Real.sin (t * u s)
  have hboundInt : IntervalIntegrable (fun s : ℝ ↦ 2 * s ^ (-1 / 2 : ℝ))
      volume 0 1 := by
    apply IntegrableOn.intervalIntegrable
    simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (apm_m97A03_integrableOn_rpow_neg_half.const_mul 2)
  have hinterval : ContinuousOn (fun t ↦ ∫ s in (0 : ℝ)..1, F t s)
      (Icc 0 1) := by
    intro t ht
    apply intervalIntegral.continuousWithinAt_of_dominated_interval
      (bound := fun s : ℝ ↦ 2 * s ^ (-1 / 2 : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with t' ht'
      have hc : ContinuousOn (F t') (Set.Ioc (0 : ℝ) 1) := by
        intro s hs
        dsimp [F]
        have hus := hu s ⟨hs.1.le, hs.2⟩
        have hs0 : s ≠ 0 := ne_of_gt hs.1
        have hdiv : ContinuousWithinAt (fun r : ℝ ↦ (t' + 3) / r)
            (Set.Ioc 0 1) s := continuousWithinAt_const.div continuousWithinAt_id hs0
        have hsqrt : ContinuousWithinAt (fun r : ℝ ↦ Real.sqrt ((t' + 3) / r))
            (Set.Ioc 0 1) s :=
          Real.continuous_sqrt.continuousAt.comp_continuousWithinAt hdiv
        have harg : ContinuousWithinAt (fun r : ℝ ↦ t' * u r)
            (Set.Ioc 0 1) s :=
          continuousWithinAt_const.mul (hus.mono Set.Ioc_subset_Icc_self)
        exact hsqrt.mul
          (Real.continuous_sin.continuousAt.comp_continuousWithinAt harg)
      simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
        (hc.aestronglyMeasurable measurableSet_Ioc :
          AEStronglyMeasurable (F t') (volume.restrict (Set.Ioc 0 1)))
    · filter_upwards [self_mem_nhdsWithin] with t' ht'
      filter_upwards [] with s hs
      exact apm_m97A03_integrand_bound
        ht' (by
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
          exact hs.1)
    · exact hboundInt
    · filter_upwards [] with s hs
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      dsimp [F]
      fun_prop
  simpa [F, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hinterval

abbrev apm_m97A03_C := C(Icc (0 : ℝ) 1, ℝ)

def apm_m97A03_extend (u : apm_m97A03_C) (x : ℝ) : ℝ :=
  u (Set.projIcc 0 1 (by norm_num) x)

lemma apm_m97A03_extend_continuous (u : apm_m97A03_C) :
    Continuous (apm_m97A03_extend u) := by
  exact u.continuous.comp continuous_projIcc

lemma apm_m97A03_extend_of_mem (u : apm_m97A03_C) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) : apm_m97A03_extend u x = u ⟨x, hx⟩ := by
  simp [apm_m97A03_extend, Set.projIcc_of_mem (by norm_num) hx]

lemma apm_m97A03_extend_zero :
    apm_m97A03_extend (0 : apm_m97A03_C) = fun _ ↦ 0 := by
  funext x
  simp [apm_m97A03_extend]

noncomputable def apm_m97A03_operator (lam : ℝ) (u : apm_m97A03_C) :
    apm_m97A03_C :=
  ⟨fun t ↦ Real.exp (t : ℝ) + lam * (∫ s in Icc (0 : ℝ) 1,
      Real.sqrt (((t : ℝ) + 3) / s) * Real.sin ((t : ℝ) * apm_m97A03_extend u s)), by
    have hcont := Real.continuous_exp.continuousOn.add
      ((apm_m97A03_integral_continuousOn (apm_m97A03_extend u)
        (apm_m97A03_extend_continuous u).continuousOn).const_mul lam)
    exact hcont.comp_continuous continuous_subtype_val (fun t ↦ t.property)⟩

lemma apm_m97A03_operator_apply (lam : ℝ) (u : apm_m97A03_C)
    (t : Icc (0 : ℝ) 1) :
    apm_m97A03_operator lam u t = Real.exp (t : ℝ) + lam *
      (∫ s in Icc (0 : ℝ) 1, Real.sqrt (((t : ℝ) + 3) / s) *
        Real.sin ((t : ℝ) * apm_m97A03_extend u s)) := rfl

lemma apm_m97A03_operator_zero_load (u : apm_m97A03_C)
    (t : Icc (0 : ℝ) 1) :
    apm_m97A03_operator 0 u t = Real.exp (t : ℝ) := by
  simp [apm_m97A03_operator_apply]

lemma apm_m97A03_integrable_integrand (u : apm_m97A03_C)
    (t : Icc (0 : ℝ) 1) :
    IntegrableOn (fun s : ℝ ↦ Real.sqrt (((t : ℝ) + 3) / s) *
      Real.sin ((t : ℝ) * apm_m97A03_extend u s)) (Icc 0 1) := by
  have hg : IntegrableOn (fun s : ℝ ↦ 2 * s ^ (-1 / 2 : ℝ)) (Icc 0 1) :=
    apm_m97A03_integrableOn_rpow_neg_half.const_mul 2
  apply Integrable.mono' hg
  · apply AEStronglyMeasurable.restrict
    have hmdiv : Measurable (fun s : ℝ ↦ ((t : ℝ) + 3) / s) :=
      measurable_const.div measurable_id
    have hmsqrt : Measurable (fun s : ℝ ↦ Real.sqrt (((t : ℝ) + 3) / s)) :=
      Real.continuous_sqrt.measurable.comp hmdiv
    have hmarg : Measurable (fun s : ℝ ↦ (t : ℝ) * apm_m97A03_extend u s) :=
      measurable_const.mul (apm_m97A03_extend_continuous u).measurable
    exact (hmsqrt.mul (Real.continuous_sin.measurable.comp hmarg)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    by_cases hs0 : s = 0
    · simp [hs0]
    · simpa only [Real.norm_eq_abs] using
        apm_m97A03_integrand_bound t.property
          (lt_of_le_of_ne hs.1 (Ne.symm hs0))

lemma apm_m97A03_operator_pointwise_dist_le (lam : ℝ)
    (u v : apm_m97A03_C) (t : Icc (0 : ℝ) 1) :
    dist (apm_m97A03_operator lam u t) (apm_m97A03_operator lam v t) ≤
      (4 * |lam|) * ‖u - v‖ := by
  let fu : ℝ → ℝ := fun s ↦ Real.sqrt (((t : ℝ) + 3) / s) *
    Real.sin ((t : ℝ) * apm_m97A03_extend u s)
  let fv : ℝ → ℝ := fun s ↦ Real.sqrt (((t : ℝ) + 3) / s) *
    Real.sin ((t : ℝ) * apm_m97A03_extend v s)
  have hsub : (∫ s in Icc (0 : ℝ) 1, fu s) - ∫ s in Icc (0 : ℝ) 1, fv s =
      ∫ s in Icc (0 : ℝ) 1, Real.sqrt (((t : ℝ) + 3) / s) *
        (Real.sin ((t : ℝ) * apm_m97A03_extend u s) -
          Real.sin ((t : ℝ) * apm_m97A03_extend v s)) := by
    rw [← integral_sub (apm_m97A03_integrable_integrand u t)
      (apm_m97A03_integrable_integrand v t)]
    apply integral_congr_ae
    filter_upwards [] with s
    ring
  have hB := apm_m97A03_integral_integrand_sub_bound t.property
    (apm_m97A03_extend u) (apm_m97A03_extend v) (B := ‖u - v‖) (by
      intro s hs
      simpa [apm_m97A03_extend_of_mem u hs, apm_m97A03_extend_of_mem v hs,
        Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm (u - v) ⟨s, hs⟩)
  rw [apm_m97A03_operator_apply, apm_m97A03_operator_apply, Real.dist_eq]
  rw [show Real.exp (t : ℝ) + lam * (∫ s in Icc (0 : ℝ) 1, fu s) -
      (Real.exp (t : ℝ) + lam * (∫ s in Icc (0 : ℝ) 1, fv s)) =
      lam * ((∫ s in Icc (0 : ℝ) 1, fu s) - ∫ s in Icc (0 : ℝ) 1, fv s) by ring,
    abs_mul, hsub]
  nlinarith [abs_nonneg lam, norm_nonneg (u - v)]

lemma apm_m97A03_operator_dist_le (lam : ℝ) (u v : apm_m97A03_C) :
    dist (apm_m97A03_operator lam u) (apm_m97A03_operator lam v) ≤
      (4 * |lam|) * dist u v := by
  apply (ContinuousMap.dist_le (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg lam))
    (dist_nonneg))).2
  intro t
  simpa [dist_eq_norm] using apm_m97A03_operator_pointwise_dist_le lam u v t

lemma apm_m97A03_operator_contracting (lam : ℝ) (hlam : |lam| < (1 / 4 : ℝ)) :
    ContractingWith ⟨4 * |lam|, mul_nonneg (by norm_num) (abs_nonneg lam)⟩
      (apm_m97A03_operator lam) := by
  constructor
  · norm_num
    linarith
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    exact apm_m97A03_operator_dist_le lam u v

theorem apm_m97a03
    (lam : ℝ) (hlam : |lam| < (1 / 4 : ℝ)) :
    ∃ u : ℝ → ℝ, apm_m97A03_isSolution lam u := by
  let K : NNReal := ⟨4 * |lam|, mul_nonneg (by norm_num) (abs_nonneg lam)⟩
  have hc : ContractingWith K (apm_m97A03_operator lam) :=
    apm_m97A03_operator_contracting lam hlam
  let w : apm_m97A03_C := ContractingWith.fixedPoint (apm_m97A03_operator lam) hc
  have hw : apm_m97A03_operator lam w = w := hc.fixedPoint_isFixedPt
  refine ⟨apm_m97A03_extend w, (apm_m97A03_extend_continuous w).continuousOn, ?_⟩
  intro t ht
  have hpoint := congrArg (fun g : apm_m97A03_C ↦ g ⟨t, ht⟩) hw
  change apm_m97A03_operator lam w ⟨t, ht⟩ = w ⟨t, ht⟩ at hpoint
  rw [apm_m97A03_operator_apply] at hpoint
  rw [apm_m97A03_extend_of_mem w ht]
  linarith
  /-
  PARTIAL boundary (codex).  The intended Banach fixed-point route is viable:
  sibling `t91A04` proves the abstract `ContractingWith.fixedPoint` wrapper,
  and Mathlib provides `Real.abs_sin_sub_sin_le`,
  `tendsto_integral_filter_of_dominated_convergence`, and
  `intervalIntegral.integral_rpow`.  However, applying those results here
  still requires a substantial concrete operator construction on
  `ContinuousMap (Icc (0 : ℝ) 1) ℝ`:

  * prove integrability on `Icc 0 1` of the singular majorant
    `s ↦ s ^ (-1 / 2 : ℝ)` and reconcile it a.e. with the statement's
    `Real.sqrt ((t + 3) / s)` (including Lean's value at `s = 0`);
  * use dominated convergence to package the parameterized singular integral
    as a continuous map (the packaged theorem
    `continuous_parametric_integral_of_continuous` does not apply because the
    kernel is not continuous at zero);
  * combine the now-proved load-bearing factor estimate
    `apm_m97A03_t_sqrt_bound` with the singular integral to establish the
    uniform sup-norm estimate with constant `4 * |lam|`, define the self-map,
    and transport the resulting fixed point back to an unrestricted function
    satisfying the frozen set-integral equation.

  Searches of `LEMMA-INDEX.md`, all closed artifacts, the nearby Hammerstein
  artifacts, `ConstructionTargets/`, and `YoungL2.lean` found no compiled
  helper combining these singular-kernel steps.  The abstract fixed-point
  theorem alone therefore does not close the goal within this pass's budget.
  The mathematical statement appears sound.

  Closer hop 1 proves `apm_m97A03_integral_rpow_neg_half`, closing the sharp
  majorant calculation `∫_[0,1] s⁻¹ᐟ² = 2` by converting the set integral to an
  interval integral and applying Mathlib's `integral_rpow`. Together with
  `apm_m97A03_t_sqrt_bound`, the numerical constant `4` is therefore fully
  accounted for. The remaining bridge is dominated parameter continuity for
  the singular kernel and its packaging as a contracting self-map of
  `ContinuousMap (Icc 0 1) ℝ`; the frozen statement is unchanged.

  CLOSER HOP 2 closes the pointwise singular-kernel reconciliation that hop 1
  left open. `apm_m97A03_sqrt_div_factor` proves away from the null endpoint
  that `sqrt ((t+3)/s) = sqrt (t+3) * s^(-1/2)`.
  `apm_m97A03_kernel_lipschitz_majorant` combines this identity with the
  existing `t * sqrt (t+3) ≤ 2` estimate, and
  `apm_m97A03_integrand_sub_bound` applies
  `Real.abs_sin_sub_sin_le` to obtain the exact pointwise domination
  `|K(t,s,u)-K(t,s,v)| ≤ 2*s^(-1/2)*|u-v|`. Thus the a.e. majorant required
  for the contraction estimate is now compiled, including its endpoint-safe
  formulation via the hypothesis `0 < s`.

  What remains is integrating this pointwise inequality while replacing
  `|u s-v s|` by the `ContinuousMap` sup norm, then proving dominated
  continuity in `t` and bundling the self-map. Searches of the parametric
  Bochner-integral and `ContinuousMap` APIs found no theorem that combines
  this a.e.-singular majorant with the required packaged continuity, so that
  final assembly remains honestly open.

  CLOSER HOP 3 compiles the integration step itself.
  `apm_m97A03_integrableOn_rpow_neg_half` transports Mathlib's open-interval
  result across `Ioo_ae_eq_Icc`, and
  `apm_m97A03_integral_integrand_sub_bound` combines the hop-2 pointwise bound,
  an arbitrary uniform bound `|u s-v s| ≤ B`, and
  `norm_integral_le_of_norm_le` to prove the exact estimate `≤ 4*B`. The
  endpoint is handled explicitly, so this is directly suitable for the
  `ContinuousMap` sup norm. What remains is dominated continuity in `t`,
  construction of the continuous self-map, and the contraction theorem.
  Searches of the parametric-integral APIs still found no packaged
  singular-kernel continuity result; the frozen statement is unchanged.

  HOP 4 found the general engine
  `intervalIntegral.continuousWithinAt_of_dominated_interval`, so the library
  gap is narrower than previously recorded.  The exact remaining local lemma
  is:

    `∀ (u : ℝ → ℝ), ContinuousOn u (Icc 0 1) →
      ContinuousOn (fun t ↦ ∫ s in Icc 0 1,
        sqrt ((t + 3) / s) * sin (t * u s)) (Icc 0 1)`.

  Its proof must instantiate that theorem with the integrable
  `s ^ (-1/2)` majorant and reconcile interval integrals with the frozen set
  integral. Once available, the continuous self-map is definable and the
  compiled `4*B` bound supplies its contraction constant `4*|lam|`.
  -/
