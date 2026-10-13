import Mathlib

/-!
# APM m95J02: The fundamental solution of the Laplacian

## Statement repairs

The typographical words "fund" and "Explan" are read as "find" and
"Explain". No mathematical repair is made. We state the result for `n ≥ 2`,
the range in which the source's logarithmic/power-law alternatives apply.

## Encoding questions

None. `EuclideanSpace ℝ (Fin n)` represents `ℝⁿ`. The delta equation is stated
in its exact weak form against smooth compactly supported test functions, and
the Poisson solution is the actual Euclidean convolution with the fundamental
solution.
-/

open MeasureTheory

noncomputable section

def apm_m95J02_sphereArea (n : ℕ) : ℝ :=
  2 * Real.rpow Real.pi ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

lemma apm_m95J02_sphereArea_two : apm_m95J02_sphereArea 2 = 2 * Real.pi := by
  simp [apm_m95J02_sphereArea, Real.Gamma_one, Real.rpow_one]

/-- The Gamma-function normalization really is a positive surface-area
constant in every positive dimension. -/
lemma apm_m95J02_sphereArea_pos {n : ℕ} (hn : 0 < n) :
    0 < apm_m95J02_sphereArea n := by
  unfold apm_m95J02_sphereArea
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  exact div_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos Real.pi_pos _))
    (Real.Gamma_pos_of_pos (div_pos hnR (by norm_num)))

lemma apm_m95J02_finrank_volume_unitBall_mul_eq_sphereArea (n : ℕ) :
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) *
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) =
      apm_m95J02_sphereArea n := by
  by_cases hn : n = 0
  · subst n
    simp [apm_m95J02_sphereArea]
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    simp only [finrank_euclideanSpace, Fintype.card_fin]
    rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball]
    simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hgamma : Real.Gamma ((n : ℝ) / 2 + 1) =
        ((n : ℝ) / 2) * Real.Gamma ((n : ℝ) / 2) := by
      rw [Real.Gamma_add_one (div_ne_zero hnR (by norm_num))]
    rw [hgamma]
    rw [show Real.sqrt Real.pi ^ n = Real.rpow Real.pi ((n : ℝ) / 2) by
      rw [← Real.rpow_natCast]
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul Real.pi_nonneg]
      congr 1
      ring]
    have hg : Real.Gamma ((n : ℝ) / 2) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
    unfold apm_m95J02_sphereArea
    field_simp

def apm_m95J02_fundamental (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if n = 2 then Real.log ‖x‖ / (2 * Real.pi)
  else -Real.rpow ‖x‖ (2 - (n : ℝ)) /
    (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

lemma apm_m95J02_fundamental_two (x : EuclideanSpace ℝ (Fin 2)) :
    apm_m95J02_fundamental 2 x = Real.log ‖x‖ / (2 * Real.pi) := by
  simp [apm_m95J02_fundamental]

/-- In dimensions above two the denominator of the power-law branch is
strictly positive, fixing its normalization and sign before the distributional
calculation. -/
lemma apm_m95J02_power_denominator_pos {n : ℕ} (hn : 2 < n) :
    0 < ((n : ℝ) - 2) * apm_m95J02_sphereArea n := by
  have hnR : (2 : ℝ) < n := by exact_mod_cast hn
  exact mul_pos (sub_pos.mpr hnR) (apm_m95J02_sphereArea_pos (by omega))

/-- Away from its pole, the higher-dimensional fundamental solution has the
expected negative sign for the convention `ΔΦ = δ`. -/
lemma apm_m95J02_fundamental_neg {n : ℕ} (hn : 2 < n)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    apm_m95J02_fundamental n x < 0 := by
  rw [apm_m95J02_fundamental, if_neg (by omega)]
  exact div_neg_of_neg_of_pos
    (neg_neg_of_pos (Real.rpow_pos_of_pos (norm_pos_iff.mpr hx) _))
    (apm_m95J02_power_denominator_pos hn)

/-- The one-variable radial profile underlying the Euclidean kernel.  Keeping
this scalar function separate isolates the remaining geometric chain rule
from the elementary power-law differentiation. -/
def apm_m95J02_radialProfile (n : ℕ) (r : ℝ) : ℝ :=
  if n = 2 then Real.log r / (2 * Real.pi)
  else -Real.rpow r (2 - (n : ℝ)) /
    (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

lemma apm_m95J02_fundamental_eq_radialProfile (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    apm_m95J02_fundamental n x = apm_m95J02_radialProfile n ‖x‖ := by
  rfl

/-- The scalar power-law profile has the expected first derivative away from
the pole.  This is the analytic input to the still-missing radial Laplacian
chain rule. -/
lemma apm_m95J02_hasDerivAt_radialProfile_of_two_lt {n : ℕ} (hn : 2 < n)
    {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (apm_m95J02_radialProfile n)
      (-( (2 - (n : ℝ)) * Real.rpow r ((2 - (n : ℝ)) - 1)) /
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) r := by
  have hfun : apm_m95J02_radialProfile n =
      fun r : ℝ => -Real.rpow r (2 - (n : ℝ)) /
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n) := by
    funext s
    simp [apm_m95J02_radialProfile, show n ≠ 2 by omega]
  rw [hfun]
  exact (Real.hasDerivAt_rpow_const (p := 2 - (n : ℝ)) (Or.inl hr)).neg.div_const
    (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

/-- The derivative displayed above is itself differentiable away from the
pole.  This supplies the second scalar derivative needed by the radial
Laplacian calculation. -/
lemma apm_m95J02_hasDerivAt_radialProfile_derivative_of_two_lt
    {n : ℕ} (hn : 2 < n) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt
      (fun s : ℝ ↦
        -((2 - (n : ℝ)) * Real.rpow s ((2 - (n : ℝ)) - 1)) /
          (((n : ℝ) - 2) * apm_m95J02_sphereArea n))
      (-((2 - (n : ℝ)) * ((2 - (n : ℝ)) - 1) *
          Real.rpow r (((2 - (n : ℝ)) - 1) - 1)) /
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) r := by
  have hp := Real.hasDerivAt_rpow_const
    (p := (2 - (n : ℝ)) - 1) (x := r) (Or.inl hr)
  simpa only [mul_assoc] using
    ((hp.const_mul (2 - (n : ℝ))).neg.div_const
      (((n : ℝ) - 2) * apm_m95J02_sphereArea n))

/-- The two scalar terms in the radial Laplacian cancel for the power-law
fundamental solution away from zero. -/
lemma apm_m95J02_power_euler_cancellation {n : ℕ} (hn : 2 < n)
    {r : ℝ} (hr : 0 < r) :
    (-((2 - (n : ℝ)) * ((2 - (n : ℝ)) - 1) *
          Real.rpow r (((2 - (n : ℝ)) - 1) - 1)) /
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) +
      ((n : ℝ) - 1) / r *
        (-((2 - (n : ℝ)) * Real.rpow r ((2 - (n : ℝ)) - 1)) /
          (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) = 0 := by
  have hnR : (2 : ℝ) < n := by exact_mod_cast hn
  have hD : (((n : ℝ) - 2) * apm_m95J02_sphereArea n) ≠ 0 :=
    ne_of_gt (apm_m95J02_power_denominator_pos hn)
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hpow : Real.rpow r ((2 - (n : ℝ)) - 1) =
      r * Real.rpow r (((2 - (n : ℝ)) - 1) - 1) := by
    change r ^ ((2 - (n : ℝ)) - 1) =
      r * r ^ (((2 - (n : ℝ)) - 1) - 1)
    rw [Real.rpow_sub_one hr0]
    field_simp
    calc
      r ^ (2 - (n : ℝ)) = r ^ ((2 : ℝ) + (-(n : ℝ))) := by ring_nf
      _ = r ^ (2 : ℝ) * r ^ (-(n : ℝ)) := Real.rpow_add hr _ _
      _ = r ^ (2 : ℕ) * r ^ (2 - (n : ℝ) - 1 - 1) := by
        apply congrArg₂ (fun a b : ℝ ↦ a * b)
        · exact Real.rpow_natCast r 2
        · congr 1
          ring
  rw [hpow]
  field_simp
  ring

/-- First derivative of the logarithmic radial branch away from its pole. -/
lemma apm_m95J02_hasDerivAt_radialProfile_two {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (apm_m95J02_radialProfile 2)
      (r⁻¹ / (2 * Real.pi)) r := by
  have hfun : apm_m95J02_radialProfile 2 =
      fun s : ℝ ↦ Real.log s / (2 * Real.pi) := by
    funext s
    simp [apm_m95J02_radialProfile]
  rw [hfun]
  exact (Real.hasDerivAt_log hr).div_const (2 * Real.pi)

/-- Second derivative of the logarithmic radial branch away from its pole. -/
lemma apm_m95J02_hasDerivAt_radialProfile_two_derivative
    {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ s⁻¹ / (2 * Real.pi))
      (-(r⁻¹ ^ 2) / (2 * Real.pi)) r := by
  convert ((hasDerivAt_id r).inv hr |>.div_const (2 * Real.pi)) using 1
  <;> simp [id]
  <;> ring

/-- The logarithmic profile satisfies the two-dimensional radial Euler
equation away from zero. -/
lemma apm_m95J02_log_euler_cancellation {r : ℝ} (hr : r ≠ 0) :
    -(r⁻¹ ^ 2) / (2 * Real.pi) +
      ((2 : ℝ) - 1) / r * (r⁻¹ / (2 * Real.pi)) = 0 := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  field_simp
  ring

/-- Both branches of the fundamental radial profile are twice continuously
differentiable at every nonzero radius.  This is deliberately local: neither
branch is smooth at the pole. -/
lemma apm_m95J02_radialProfile_contDiffAt_two
    {n : ℕ} {r : ℝ} (hr : r ≠ 0) :
    ContDiffAt ℝ 2 (apm_m95J02_radialProfile n) r := by
  unfold apm_m95J02_radialProfile
  split_ifs
  · exact (Real.contDiffAt_log.mpr hr).div_const (2 * Real.pi)
  · exact (Real.contDiffAt_rpow_const (Or.inl hr)).neg.div_const
      (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

/-- The Fréchet derivative of the Euclidean norm away from the origin,
written as the normalized Riesz functional. -/
lemma apm_m95J02_hasFDerivAt_norm
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖)
      ((‖x‖⁻¹) • (innerSL ℝ x)) x := by
  have hsq := hasStrictFDerivAt_norm_sq x
  have hspos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsne : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 hspos.ne'
  have h := hsq.hasFDerivAt.sqrt hsne
  have hfun : (fun z : EuclideanSpace ℝ (Fin n) ↦ Real.sqrt (‖z‖ ^ 2)) =
      fun z ↦ ‖z‖ := by
    funext z
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg z)]
  rw [hfun] at h
  convert h using 1
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hspos]
  ext z
  simp [smul_smul]
  field_simp

lemma apm_m95J02_fderiv_norm_apply
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (z : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) ↦ ‖w‖) x z =
      inner ℝ x z / ‖x‖ := by
  rw [(apm_m95J02_hasFDerivAt_norm hx).fderiv]
  simp [div_eq_inv_mul, mul_comm]

/-- The squared directional derivatives of the radius have trace one in an
orthonormal coordinate frame. -/
lemma apm_m95J02_sum_sq_fderiv_norm
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      (fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) ↦ ‖w‖) x
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i)) ^ 2 = 1 := by
  simp_rw [apm_m95J02_fderiv_norm_apply hx]
  simp_rw [div_pow]
  rw [← Finset.sum_div, (stdOrthonormalBasis ℝ
    (EuclideanSpace ℝ (Fin n))).sum_sq_inner_left]
  exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

/-- Derivative of the reciprocal radius, the scalar factor in the Hessian of
the Euclidean norm. -/
lemma apm_m95J02_hasFDerivAt_inv_norm
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖x‖) ^ 2)⁻¹)).comp
        ((‖x‖⁻¹) • (innerSL ℝ x))) x := by
  exact (hasFDerivAt_inv (norm_ne_zero_iff.mpr hx)).comp x
    (apm_m95J02_hasFDerivAt_norm hx)

lemma apm_m95J02_fderiv_inv_norm_apply
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (z : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) ↦ ‖w‖⁻¹) x z =
      -(inner ℝ x z) / ‖x‖ ^ 3 := by
  rw [(apm_m95J02_hasFDerivAt_inv_norm hx).fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, div_eq_mul_inv]
  field_simp

/-- The normalized Riesz map, whose derivative is the Hessian of the norm,
is differentiable away from the origin. -/
lemma apm_m95J02_hasFDerivAt_normGradient
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∃ G' : EuclideanSpace ℝ (Fin n) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ),
      HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖⁻¹ • innerSL ℝ z) G' x := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    (innerSL ℝ).toLinearMap.toContinuousLinearMap
  have hL : HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) ↦ innerSL ℝ z) L x := by
    exact L.hasFDerivAt
  exact ⟨_, (apm_m95J02_hasFDerivAt_inv_norm hx).smul hL⟩

/-- Diagonal value of the Hessian of the Euclidean norm. -/
lemma apm_m95J02_fderiv_normGradient_apply_self
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (z : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ
        (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖⁻¹ • innerSL ℝ y) x z z =
      ‖z‖ ^ 2 / ‖x‖ - (inner ℝ x z) ^ 2 / ‖x‖ ^ 3 := by
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    (innerSL ℝ).toLinearMap.toContinuousLinearMap
  have hL : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin n) ↦ innerSL ℝ y) L x := L.hasFDerivAt
  have h := (apm_m95J02_hasFDerivAt_inv_norm hx).smul hL
  let G' : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    ‖x‖⁻¹ • L +
      ((ContinuousLinearMap.toSpanSingleton ℝ (-((‖x‖) ^ 2)⁻¹)).comp
        ((‖x‖⁻¹) • (innerSL ℝ x))).smulRight (innerSL ℝ x)
  have h' : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖⁻¹ • innerSL ℝ y) G' x := by
    simpa only [Pi.smul_apply, G'] using h
  rw [h'.fderiv]
  simp [G', L, ContinuousLinearMap.toSpanSingleton_apply, div_eq_mul_inv,
    innerSL_apply_apply]
  field_simp
  change ‖x‖ ^ 2 * inner ℝ z z + -(inner ℝ x z) ^ 2 =
    ‖x‖ ^ 2 * ‖z‖ ^ 2 - (inner ℝ x z) ^ 2
  rw [real_inner_self_eq_norm_sq]
  ring

/-- Trace of the Hessian of the Euclidean radius. -/
lemma apm_m95J02_trace_normHessian
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    ∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      fderiv ℝ
        (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y‖⁻¹ • innerSL ℝ y) x
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i)
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i) =
      ((n : ℝ) - 1) / ‖x‖ := by
  simp_rw [apm_m95J02_fderiv_normGradient_apply_self hx]
  rw [Finset.sum_sub_distrib]
  simp_rw [(stdOrthonormalBasis ℝ
    (EuclideanSpace ℝ (Fin n))).norm_eq_one]
  simp only [one_pow, Finset.sum_div]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hsdiv :
      (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
        (inner ℝ x ((stdOrthonormalBasis ℝ
          (EuclideanSpace ℝ (Fin n))) i)) ^ 2 / ‖x‖ ^ 3) =
        ‖x‖ ^ 2 / ‖x‖ ^ 3 := by
    rw [← Finset.sum_div]
    rw [(stdOrthonormalBasis ℝ
      (EuclideanSpace ℝ (Fin n))).sum_sq_inner_left]
  rw [hsdiv]
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
    simp
  rw [hfinrank]
  field_simp
  congr 1
  simp only [nsmul_eq_mul, one_div]
  change ‖x‖ * ((n : ℝ) * ‖x‖⁻¹) = (n : ℝ)
  calc
    ‖x‖ * ((n : ℝ) * ‖x‖⁻¹) = (n : ℝ) * (‖x‖ * ‖x‖⁻¹) := by ring
    _ = (n : ℝ) := by rw [mul_inv_cancel₀ hxnorm, mul_one]

/-- First derivative of a general radial composition, in the form used by
the second-order product rule. -/
lemma apm_m95J02_fderiv_radial_apply
    {n : ℕ} (v : ℝ → ℝ) (x z : EuclideanSpace ℝ (Fin n))
    (hv : DifferentiableAt ℝ v ‖x‖) (hx : x ≠ 0) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ v ‖y‖) x z =
      deriv v ‖x‖ * (inner ℝ x z / ‖x‖) := by
  have hn := (contDiffAt_norm ℝ (n := (1 : WithTop ℕ∞)) hx).differentiableAt
    (by norm_num)
  change fderiv ℝ (v ∘ norm) x z = _
  rw [fderiv_comp x hv hn]
  rw [ContinuousLinearMap.comp_apply]
  rw [fderiv_eq_deriv_mul]
  rw [apm_m95J02_fderiv_norm_apply hx]

/-- The radial gradient is differentiable away from the origin.  This is the
second-order chain-rule interface needed to compute its trace. -/
lemma apm_m95J02_differentiableAt_fderiv_radial
    {n : ℕ} (v : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hv : ContDiff ℝ 2 v) (hx : x ≠ 0) :
    DifferentiableAt ℝ
      (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ v ‖y‖)) x := by
  let A : EuclideanSpace ℝ (Fin n) → ℝ := fun y => deriv v ‖y‖
  let G : EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun y => ‖y‖⁻¹ • innerSL ℝ y
  have hA : DifferentiableAt ℝ A x := by
    exact (hv.differentiable_deriv_two ‖x‖).comp x
      (apm_m95J02_hasFDerivAt_norm hx).differentiableAt
  obtain ⟨G', hG⟩ := apm_m95J02_hasFDerivAt_normGradient hx
  have hB : DifferentiableAt ℝ (fun y => A y • G y) x :=
    hA.smul hG.differentiableAt
  have hvdiff : Differentiable ℝ v := hv.differentiable (by norm_num)
  have heq : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ v ‖y‖) =ᶠ[nhds x]
      (fun y => A y • G y) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    ext z
    rw [apm_m95J02_fderiv_radial_apply v y z (hvdiff ‖y‖) hy]
    simp [A, G, div_eq_mul_inv, mul_comm, mul_left_comm]
  exact hB.congr_of_eventuallyEq heq

lemma apm_m95J02_fderiv_deriv_comp_norm_apply
    {n : ℕ} (v : ℝ → ℝ) (x z : EuclideanSpace ℝ (Fin n))
    (hv : ContDiff ℝ 2 v) (hx : x ≠ 0) :
    fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) => deriv v ‖y‖) x z =
      deriv (deriv v) ‖x‖ * (inner ℝ x z / ‖x‖) := by
  have hd := (hv.differentiable_deriv_two ‖x‖).hasDerivAt
  have hc := hd.comp_hasFDerivAt x (apm_m95J02_hasFDerivAt_norm hx)
  change HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => deriv v ‖y‖) _ x at hc
  rw [hc.fderiv]
  simp [ContinuousLinearMap.toSpanSingleton_apply, div_eq_mul_inv,
    mul_comm, mul_left_comm]

lemma apm_m95J02_second_radial_diagonal
    {n : ℕ} (v : ℝ → ℝ) (x z : EuclideanSpace ℝ (Fin n))
    (hv : ContDiffAt ℝ 2 v ‖x‖) (hx : x ≠ 0) :
    fderiv ℝ (fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ v ‖y‖)) x z z =
      deriv (deriv v) ‖x‖ * (inner ℝ x z / ‖x‖) ^ 2 +
        deriv v ‖x‖ *
          fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦
            ‖y‖⁻¹ • innerSL ℝ y) x z z := by
  let A : EuclideanSpace ℝ (Fin n) → ℝ := fun y => deriv v ‖y‖
  let G : EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun y => ‖y‖⁻¹ • innerSL ℝ y
  have hd := ((ContDiffAt.derivWithin (m := 1) hv (by norm_num)).differentiableAt
    (by norm_num)).hasDerivAt
  have hA := hd.comp_hasFDerivAt x (apm_m95J02_hasFDerivAt_norm hx)
  change HasFDerivAt A _ x at hA
  obtain ⟨G', hG⟩ := apm_m95J02_hasFDerivAt_normGradient hx
  have hprod := hA.smul hG
  change HasFDerivAt (fun y => A y • G y) _ x at hprod
  have hev : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 v ‖y‖ :=
    continuous_norm.continuousAt.tendsto.eventually
      (hv.eventually (by norm_num))
  have heq : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin n) ↦ v ‖y‖) =ᶠ[nhds x]
      (fun y => A y • G y) := by
    filter_upwards [eventually_ne_nhds hx, hev] with y hy hvy
    ext w
    rw [apm_m95J02_fderiv_radial_apply v y w
      (hvy.differentiableAt (by norm_num)) hy]
    simp [A, G, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [heq.fderiv_eq, hprod.fderiv]
  rw [hG.fderiv]
  simp [A, G, ContinuousLinearMap.toSpanSingleton_apply, div_eq_mul_inv,
    mul_comm, mul_left_comm]
  ring

lemma apm_m95J02_laplacian_radial
    {n : ℕ} (v : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (hv : ContDiffAt ℝ 2 v ‖x‖) (hx : x ≠ 0) :
    Laplacian.laplacian (fun z : EuclideanSpace ℝ (Fin n) ↦ v ‖z‖) x =
      iteratedDeriv 2 v ‖x‖ +
        ((n : ℝ) - 1) / ‖x‖ * deriv v ‖x‖ := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  simp_rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [apm_m95J02_second_radial_diagonal v x _ hv hx]
  rw [Finset.sum_add_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [← apm_m95J02_fderiv_norm_apply hx]
  rw [apm_m95J02_sum_sq_fderiv_norm hx]
  rw [apm_m95J02_trace_normHessian hx]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one]
  ring

/-- The normalized fundamental kernel is harmonic away from its pole. -/
lemma apm_m95J02_laplacian_fundamental_eq_zero
    {n : ℕ} (hn : 2 ≤ n) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    Laplacian.laplacian (apm_m95J02_fundamental n) x = 0 := by
  change Laplacian.laplacian
    (fun y : EuclideanSpace ℝ (Fin n) => apm_m95J02_radialProfile n ‖y‖) x = 0
  rw [apm_m95J02_laplacian_radial (apm_m95J02_radialProfile n) x
    (apm_m95J02_radialProfile_contDiffAt_two (norm_ne_zero_iff.mpr hx)) hx]
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rcases hn.eq_or_lt with hn2 | hn2
  · subst n
    let d : ℝ → ℝ := fun s => s⁻¹ / (2 * Real.pi)
    have hfirst : deriv (apm_m95J02_radialProfile 2) ‖x‖ = d ‖x‖ :=
      (apm_m95J02_hasDerivAt_radialProfile_two hr).deriv
    have hev : deriv (apm_m95J02_radialProfile 2) =ᶠ[nhds ‖x‖] d := by
      filter_upwards [eventually_ne_nhds hr] with s hs
      exact (apm_m95J02_hasDerivAt_radialProfile_two hs).deriv
    have hit : iteratedDeriv 2 (apm_m95J02_radialProfile 2) =
        deriv (deriv (apm_m95J02_radialProfile 2)) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]
    rw [hit]
    rw [hev.deriv_eq,
      (apm_m95J02_hasDerivAt_radialProfile_two_derivative hr).deriv,
      hfirst]
    exact apm_m95J02_log_euler_cancellation hr
  · let d : ℝ → ℝ := fun s =>
        -((2 - (n : ℝ)) * Real.rpow s ((2 - (n : ℝ)) - 1)) /
          (((n : ℝ) - 2) * apm_m95J02_sphereArea n)
    have hfirst : deriv (apm_m95J02_radialProfile n) ‖x‖ = d ‖x‖ :=
      (apm_m95J02_hasDerivAt_radialProfile_of_two_lt hn2 hr).deriv
    have hev : deriv (apm_m95J02_radialProfile n) =ᶠ[nhds ‖x‖] d := by
      filter_upwards [eventually_ne_nhds hr] with s hs
      exact (apm_m95J02_hasDerivAt_radialProfile_of_two_lt hn2 hs).deriv
    have hit : iteratedDeriv 2 (apm_m95J02_radialProfile n) =
        deriv (deriv (apm_m95J02_radialProfile n)) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]
    rw [hit]
    rw [hev.deriv_eq,
      (apm_m95J02_hasDerivAt_radialProfile_derivative_of_two_lt hn2 hr).deriv,
      hfirst]
    exact apm_m95J02_power_euler_cancellation hn2 (norm_pos_iff.mpr hx)

/-- The singular kernel is measurable; the remaining analytic issue for its
convolution is local integrability at the pole, not measurability. -/
lemma apm_m95J02_fundamental_measurable (n : ℕ) :
    Measurable (apm_m95J02_fundamental n) := by
  apply measurable_of_continuousOn_compl_singleton 0
  intro x hx
  change ContinuousWithinAt
    (fun y : EuclideanSpace ℝ (Fin n) => apm_m95J02_radialProfile n ‖y‖)
    ({0}ᶜ) x
  exact ((apm_m95J02_radialProfile_contDiffAt_two
    (norm_ne_zero_iff.mpr hx)).continuousAt.comp
      continuous_norm.continuousAt).continuousWithinAt

/-- On compact sets separated from the pole the kernel is integrable by
ordinary continuity.  The only missing local-integrability case is therefore
a neighborhood containing the origin. -/
lemma apm_m95J02_fundamental_integrableOn_compact_away
    {n : ℕ} {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (h0 : 0 ∉ K) :
    IntegrableOn (apm_m95J02_fundamental n) K := by
  apply ContinuousOn.integrableOn_compact hK
  intro x hx
  have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
  change ContinuousWithinAt
    (fun y : EuclideanSpace ℝ (Fin n) => apm_m95J02_radialProfile n ‖y‖) K x
  exact ((apm_m95J02_radialProfile_contDiffAt_two
    (norm_ne_zero_iff.mpr hx0)).continuousAt.comp
      continuous_norm.continuousAt).continuousWithinAt

/-- Polar coordinates reduce the only singular integrability question to a
one-dimensional weighted integral.  The cutoff is the open unit ball, so its
radial representative is exactly the displayed `if`. -/
lemma apm_m95J02_integrable_unitBallCutoff_iff (n : ℕ) (hn : 0 < n) :
    Integrable
        (fun x : EuclideanSpace ℝ (Fin n) =>
          if ‖x‖ < 1 then apm_m95J02_fundamental n x else 0) ↔
      IntegrableOn
        (fun r : ℝ => r ^ (Module.finrank ℝ
              (EuclideanSpace ℝ (Fin n)) - 1) •
            (if r < 1 then apm_m95J02_radialProfile n r else 0))
        (Set.Ioi 0) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  simpa only [apm_m95J02_fundamental_eq_radialProfile] using
    (MeasureTheory.integrable_fun_norm_addHaar
      (volume : Measure (EuclideanSpace ℝ (Fin n)))
      (f := fun r : ℝ =>
        if r < 1 then apm_m95J02_radialProfile n r else 0))

lemma apm_m95J02_integrableOn_Ioi_cutoff
    {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioo 0 1)) :
    IntegrableOn (fun r => if r < 1 then f r else 0) (Set.Ioi 0) := by
  have hi : Integrable (Set.indicator (Set.Ioo 0 1) f) :=
    hf.integrable_indicator measurableSet_Ioo
  apply (hi.integrableOn).congr_fun ?_ measurableSet_Ioi
  intro r hr
  simp only [Set.mem_Ioi] at hr
  by_cases h1 : r < 1
  · simp [h1, hr]
  · simp [h1, hr]

lemma apm_m95J02_weightedProfile_two_integrable :
    IntegrableOn
      (fun r : ℝ => r ^ (2 - 1) • apm_m95J02_radialProfile 2 r)
      (Set.Ioo 0 1) := by
  have hlog : IntegrableOn (fun r : ℝ => r * Real.log r) (Set.Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
      (Real.continuous_mul_log.intervalIntegrable 0 1)
  apply IntegrableOn.congr_fun (hlog.const_mul ((2 * Real.pi)⁻¹)) ?_
    measurableSet_Ioo
  intro r hr
  simp [apm_m95J02_radialProfile, smul_eq_mul, div_eq_mul_inv]
  ring

lemma apm_m95J02_integrable_unitBallCutoff_two :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        if ‖x‖ < 1 then apm_m95J02_fundamental 2 x else 0) := by
  rw [apm_m95J02_integrable_unitBallCutoff_iff 2 (by norm_num)]
  have h := apm_m95J02_integrableOn_Ioi_cutoff
    apm_m95J02_weightedProfile_two_integrable
  simpa [Module.finrank_pi_fintype, smul_ite] using h

lemma apm_m95J02_weightedProfile_of_two_lt
    {n : ℕ} (hn : 2 < n) {r : ℝ} (hr : 0 < r) :
    r ^ (n - 1) • apm_m95J02_radialProfile n r =
      -r / (((n : ℝ) - 2) * apm_m95J02_sphereArea n) := by
  rw [apm_m95J02_radialProfile, if_neg (by omega)]
  simp only [smul_eq_mul]
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hpow : r ^ (n - 1) * r ^ (2 - (n : ℝ)) = r := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_add hr ((n - 1 : ℕ) : ℝ) (2 - (n : ℝ))]
    rw [hcast]
    convert Real.rpow_one r using 2 <;> ring
  calc
    r ^ (n - 1) * (-Real.rpow r (2 - (n : ℝ)) /
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) =
        -(r ^ (n - 1) * Real.rpow r (2 - (n : ℝ))) /
          (((n : ℝ) - 2) * apm_m95J02_sphereArea n) := by ring
    _ = _ := by
      congr 2

lemma apm_m95J02_weightedProfile_integrable_of_two_lt
    {n : ℕ} (hn : 2 < n) :
    IntegrableOn
      (fun r : ℝ => r ^ (n - 1) • apm_m95J02_radialProfile n r)
      (Set.Ioo 0 1) := by
  have hlin : IntegrableOn
      (fun r : ℝ => -r /
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) (Set.Ioo 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mp
      ((continuous_id.neg.div_const
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n)).intervalIntegrable 0 1)
  apply hlin.congr_fun ?_ measurableSet_Ioo
  intro r hr
  exact (apm_m95J02_weightedProfile_of_two_lt hn hr.1).symm

lemma apm_m95J02_integrable_unitBallCutoff_of_two_lt
    {n : ℕ} (hn : 2 < n) :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        if ‖x‖ < 1 then apm_m95J02_fundamental n x else 0) := by
  rw [apm_m95J02_integrable_unitBallCutoff_iff n (by omega)]
  have h := apm_m95J02_integrableOn_Ioi_cutoff
    (apm_m95J02_weightedProfile_integrable_of_two_lt hn)
  simpa [Module.finrank_pi_fintype, smul_ite] using h

lemma apm_m95J02_integrable_unitBallCutoff
    {n : ℕ} (hn : 2 ≤ n) :
    Integrable
      (fun x : EuclideanSpace ℝ (Fin n) =>
        if ‖x‖ < 1 then apm_m95J02_fundamental n x else 0) := by
  rcases hn.eq_or_lt with rfl | hn
  · exact apm_m95J02_integrable_unitBallCutoff_two
  · exact apm_m95J02_integrable_unitBallCutoff_of_two_lt hn

lemma apm_m95J02_fundamental_integrableOn_unitBall
    {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn (apm_m95J02_fundamental n)
      (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  have hc := (apm_m95J02_integrable_unitBallCutoff hn).integrableOn
    (s := Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)
  apply hc.congr_fun ?_ Metric.isOpen_ball.measurableSet
  intro x hx
  have hnorm : ‖x‖ < 1 := by simpa [Metric.mem_ball] using hx
  simp [hnorm]

lemma apm_m95J02_fundamental_integrableOn_compact
    {n : ℕ} (hn : 2 ≤ n) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) :
    IntegrableOn (apm_m95J02_fundamental n) K := by
  let B : Set (EuclideanSpace ℝ (Fin n)) := Metric.ball 0 1
  have hin : IntegrableOn (apm_m95J02_fundamental n) (K ∩ B) :=
    (apm_m95J02_fundamental_integrableOn_unitBall hn).mono_set (by
      intro x hx
      exact hx.2)
  have hKout : IsCompact (K ∩ Bᶜ) :=
    hK.inter_right Metric.isOpen_ball.isClosed_compl
  have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ K ∩ Bᶜ := by
    intro h
    exact h.2 (by simp [B])
  have hout : IntegrableOn (apm_m95J02_fundamental n) (K ∩ Bᶜ) :=
    apm_m95J02_fundamental_integrableOn_compact_away hKout hzero
  apply (hin.union hout).mono_set
  intro x hx
  by_cases hB : x ∈ B
  · exact Or.inl ⟨hx, hB⟩
  · exact Or.inr ⟨hx, hB⟩

lemma apm_m95J02_fundamental_locallyIntegrable
    {n : ℕ} (hn : 2 ≤ n) :
    LocallyIntegrable (apm_m95J02_fundamental n) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact apm_m95J02_fundamental_integrableOn_compact hn hK

def apm_m95J02_poissonSolution (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ y, apm_m95J02_fundamental n (x - y) * f y

open scoped Convolution

lemma apm_m95J02_poissonSolution_eq_convolution
    (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    apm_m95J02_poissonSolution n f =
      f ⋆[ContinuousLinearMap.lsmul ℝ ℝ] apm_m95J02_fundamental n := by
  funext x
  rw [MeasureTheory.convolution_lsmul]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [apm_m95J02_poissonSolution, smul_eq_mul, mul_comm]

lemma apm_m95J02_poissonSolution_contDiff
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) :
    ContDiff ℝ 2 (apm_m95J02_poissonSolution n f) := by
  rw [apm_m95J02_poissonSolution_eq_convolution]
  exact hfc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hf.of_le (by norm_cast))
    (apm_m95J02_fundamental_locallyIntegrable hn)

lemma apm_m95J02_fderiv_poissonSolution
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (apm_m95J02_poissonSolution n f) x =
      ((fderiv ℝ f) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n))]
        apm_m95J02_fundamental n) x := by
  rw [apm_m95J02_poissonSolution_eq_convolution]
  exact (hfc.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (hf.of_le (by norm_cast))
    (apm_m95J02_fundamental_locallyIntegrable hn) x).fderiv

lemma apm_m95J02_fderiv_fderiv_poissonSolution
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fderiv ℝ (apm_m95J02_poissonSolution n f)) x =
      ∫ y, apm_m95J02_fundamental n (x - y) •
        fderiv ℝ (fderiv ℝ f) y := by
  have heq : fderiv ℝ (apm_m95J02_poissonSolution n f) =
      (fderiv ℝ f) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n))]
        apm_m95J02_fundamental n := by
    funext z
    exact apm_m95J02_fderiv_poissonSolution hn f hf hfc z
  rw [heq]
  have h := ((hfc.fderiv ℝ).hasFDerivAt_convolution_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL
      (EuclideanSpace ℝ (Fin n)))
    (hf.fderiv_right (m := 1) (by norm_cast))
    (apm_m95J02_fundamental_locallyIntegrable hn) x).fderiv
  rw [h]
  rw [MeasureTheory.convolution]
  apply integral_congr_ae
  filter_upwards [] with y
  ext z w
  simp [mul_comm]

lemma apm_m95J02_diagonal_hessian_integrable
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x e : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => apm_m95J02_fundamental n (x - y) *
      fderiv ℝ (fderiv ℝ f) y e e) := by
  let d : (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) → ℝ := fun A => A e e
  have hd0 : d 0 = 0 := by simp [d]
  have hc : HasCompactSupport (fun y => d (fderiv ℝ (fderiv ℝ f) y)) :=
    ((hfc.fderiv ℝ).fderiv ℝ).comp_left hd0
  have hd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (by norm_cast)
  have hdd : Continuous (fderiv ℝ (fderiv ℝ f)) :=
    (hd.fderiv_right (m := 0) (by norm_cast)).continuous
  have hdcont : Continuous d := by
    fun_prop
  have hi := hc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hdcont.comp hdd) (apm_m95J02_fundamental_locallyIntegrable hn) x
  apply hi.congr
  filter_upwards [] with y
  simp [d, mul_comm]

lemma apm_m95J02_fderiv_poissonSolution_apply
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x e : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (apm_m95J02_poissonSolution n f) x e =
      ∫ y, apm_m95J02_fundamental n (x - y) * fderiv ℝ f y e := by
  rw [apm_m95J02_fderiv_poissonSolution hn f hf hfc x]
  rw [MeasureTheory.convolution]
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.lsmul ℝ ℝ).precompL
      (EuclideanSpace ℝ (Fin n))
  have hi := (hfc.fderiv ℝ).convolutionExists_left L
    (hf.fderiv_right (m := 0) (by norm_cast)).continuous
    (apm_m95J02_fundamental_locallyIntegrable hn) x
  rw [ContinuousLinearMap.integral_apply hi e]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [L, mul_comm]

lemma apm_m95J02_directionalFDeriv_hasCompactSupport
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfc : HasCompactSupport f) (e : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (fun y => fderiv ℝ f y e) := by
  let d : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) → ℝ := fun A => A e
  have hd0 : d 0 = 0 := by simp [d]
  simpa only [d] using (hfc.fderiv ℝ).comp_left hd0

lemma apm_m95J02_directionalFDeriv_contDiff
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (e : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (fun y => fderiv ℝ f y e) := by
  exact (hf.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const

lemma apm_m95J02_fderiv_directionalFDeriv
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (e y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => fderiv ℝ f z e) y =
      (fderiv ℝ (fderiv ℝ f) y).flip e := by
  rw [fderiv_clm_apply
    ((hf.fderiv_right (m := 1) (by norm_cast)).differentiable (by norm_num) y)
    (differentiableAt_const (c := e))]
  simp

lemma apm_m95J02_directional_poisson_eq_convolution
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (e : EuclideanSpace ℝ (Fin n)) :
    (fun z => fderiv ℝ (apm_m95J02_poissonSolution n f) z e) =
      (fun y => fderiv ℝ f y e) ⋆[ContinuousLinearMap.lsmul ℝ ℝ]
        apm_m95J02_fundamental n := by
  funext z
  rw [apm_m95J02_fderiv_poissonSolution_apply hn f hf hfc z e]
  rw [MeasureTheory.convolution]
  apply integral_congr_ae
  filter_upwards [] with y
  simp [mul_comm]

lemma apm_m95J02_fderiv_directional_poisson
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x e : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => fderiv ℝ (apm_m95J02_poissonSolution n f) z e) x =
      ((fderiv ℝ (fun y => fderiv ℝ f y e)) ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompL
          (EuclideanSpace ℝ (Fin n))]
        apm_m95J02_fundamental n) x := by
  rw [apm_m95J02_directional_poisson_eq_convolution hn f hf hfc e]
  exact ((apm_m95J02_directionalFDeriv_hasCompactSupport f hfc e).hasFDerivAt_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (apm_m95J02_directionalFDeriv_contDiff f hf e)
      (apm_m95J02_fundamental_locallyIntegrable hn) x).fderiv

lemma apm_m95J02_second_diagonal_poissonSolution
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x e : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => fderiv ℝ (apm_m95J02_poissonSolution n f) z e) x e =
      ∫ y, apm_m95J02_fundamental n (x - y) *
        fderiv ℝ (fderiv ℝ f) y e e := by
  rw [apm_m95J02_fderiv_directional_poisson hn f hf hfc x e]
  rw [MeasureTheory.convolution]
  let L : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.lsmul ℝ ℝ).precompL
      (EuclideanSpace ℝ (Fin n))
  have hi :=
    ((apm_m95J02_directionalFDeriv_hasCompactSupport f hfc e).fderiv ℝ).convolutionExists_left L
      ((apm_m95J02_directionalFDeriv_contDiff f hf e).fderiv_right
        (m := 0) (by norm_num)).continuous
      (apm_m95J02_fundamental_locallyIntegrable hn) x
  rw [ContinuousLinearMap.integral_apply hi e]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [apm_m95J02_fderiv_directionalFDeriv f (hf.of_le (by norm_cast)) e y]
  simp [L, mul_comm]

lemma apm_m95J02_laplacian_poissonSolution_eq_integral
    {n : ℕ} (hn : 2 ≤ n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (apm_m95J02_poissonSolution n f) x =
      ∫ y, apm_m95J02_fundamental n (x - y) * Laplacian.laplacian f y := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
    (apm_m95J02_poissonSolution n f)) x]
  simp_rw [iteratedFDeriv_two_apply]
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  have hp : ContDiff ℝ 2 (apm_m95J02_poissonSolution n f) :=
    (apm_m95J02_poissonSolution_contDiff hn f hf hfc).of_le (by norm_cast)
  have hdiag (i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
      fderiv ℝ (fderiv ℝ (apm_m95J02_poissonSolution n f)) x (b i) (b i) =
        ∫ y, apm_m95J02_fundamental n (x - y) *
          fderiv ℝ (fderiv ℝ f) y (b i) (b i) := by
    have hd := congrArg (fun A => A (b i))
      (apm_m95J02_fderiv_directionalFDeriv
        (apm_m95J02_poissonSolution n f) hp (b i) x)
    simp at hd
    rw [← hd]
    exact apm_m95J02_second_diagonal_poissonSolution hn f hf hfc x (b i)
  change (∑ i, fderiv ℝ (fderiv ℝ (apm_m95J02_poissonSolution n f)) x
    (b i) (b i)) = _
  simp_rw [hdiag]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards [] with y
    rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) y]
    simp_rw [iteratedFDeriv_two_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [Finset.mul_sum]
  · intro i hi
    exact apm_m95J02_diagonal_hessian_integrable hn f hf hfc x (b i)

lemma apm_m95J02_integral_comp_subLeft
    {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y, g (x - y)) = ∫ y, g y := by
  have hp : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin n) => x - y)
      volume volume := by
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      (MeasureTheory.measurePreserving_add_left volume x).comp
        (Measure.measurePreserving_neg volume)
  exact hp.integral_comp (Homeomorph.subLeft x).measurableEmbedding g

lemma apm_m95J02_laplacian_comp_subLeft
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (x y : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (fun z => f (x - z)) y =
      Laplacian.laplacian f (x - y) := by
  let N : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    -(ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
  have hfun : (fun z => f (x - z)) = (fun w => f (x + w)) ∘ N := by
    funext z
    simp [N, sub_eq_add_neg]
  rw [hfun]
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
    ((fun w => f (x + w)) ∘ N)) y]
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) (x - y)]
  have hshift : ContDiff ℝ 2 (fun w => f (x + w)) :=
    hf.comp (contDiff_const.add contDiff_id)
  apply Finset.sum_congr rfl
  intro i hi
  rw [N.iteratedFDeriv_comp_right hshift y (i := 2) (by norm_num)]
  rw [iteratedFDeriv_comp_add_left]
  simp only [N, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply]
  rw [show (fun j : Fin 2 =>
      -(![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
          (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i] j)) =
      ![-(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
        -(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i] by
        ext j
        fin_cases j <;> simp]
  rw [iteratedFDeriv_two_apply]
  rw [iteratedFDeriv_two_apply]
  simp [sub_eq_add_neg]

lemma apm_m95J02_translatedTest_contDiff
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => f (x - y)) := by
  exact hf.comp (contDiff_const.sub contDiff_id)

lemma apm_m95J02_translatedTest_hasCompactSupport
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (fun y => f (x - y)) := by
  exact hf.comp_homeomorph (Homeomorph.subLeft x)

lemma apm_m95J02_poisson_eq_of_weakIdentity
    {n : ℕ} (hn : 2 ≤ n)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∫ x, apm_m95J02_fundamental n x * Laplacian.laplacian φ x) = φ 0)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (apm_m95J02_poissonSolution n f) x = f x := by
  rw [apm_m95J02_laplacian_poissonSolution_eq_integral hn f hf hfc x]
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun y =>
    apm_m95J02_fundamental n (x - y) * Laplacian.laplacian f y
  rw [← apm_m95J02_integral_comp_subLeft g x]
  have hw := hweak (fun z => f (x - z))
    (apm_m95J02_translatedTest_contDiff hf x)
    (apm_m95J02_translatedTest_hasCompactSupport hfc x)
  calc
    (∫ y, g (x - y)) =
        ∫ z, apm_m95J02_fundamental n z *
          Laplacian.laplacian (fun w => f (x - w)) z := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [g, sub_sub_cancel]
      rw [apm_m95J02_laplacian_comp_subLeft f (hf.of_le (by norm_cast)) x z]
    _ = f x := by simpa using hw

lemma apm_m95J02_weakIdentity_of_regularization
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (K ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hkernel : Filter.Tendsto
      (fun k => ∫ x, K k x * Laplacian.laplacian φ x)
      Filter.atTop (nhds (∫ x, apm_m95J02_fundamental n x *
        Laplacian.laplacian φ x)))
    (hgreen : ∀ k,
      (∫ x, K k x * Laplacian.laplacian φ x) =
        ∫ x, ρ k x * φ x)
    (hdensity : Filter.Tendsto (fun k => ∫ x, ρ k x * φ x)
      Filter.atTop (nhds (φ 0))) :
    (∫ x, apm_m95J02_fundamental n x * Laplacian.laplacian φ x) = φ 0 := by
  have hkernel' : Filter.Tendsto
      (fun k => ∫ x, K k x * Laplacian.laplacian φ x)
      Filter.atTop (nhds (φ 0)) := by
    convert hdensity using 1
    funext k
    exact hgreen k
  exact tendsto_nhds_unique hkernel hkernel'

lemma apm_m95J02_weakIdentity_of_regularization_family
    {n : ℕ}
    (K ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hkernel : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        Filter.Tendsto (fun k => ∫ x, K k x * Laplacian.laplacian φ x)
          Filter.atTop (nhds (∫ x, apm_m95J02_fundamental n x *
            Laplacian.laplacian φ x)))
    (hgreen : ∀ (φ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → ∀ k,
        (∫ x, K k x * Laplacian.laplacian φ x) =
          ∫ x, ρ k x * φ x)
    (hdensity : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        Filter.Tendsto (fun k => ∫ x, ρ k x * φ x) Filter.atTop (nhds (φ 0))) :
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∫ x, apm_m95J02_fundamental n x * Laplacian.laplacian φ x) = φ 0 := by
  intro φ hφ hφc
  exact apm_m95J02_weakIdentity_of_regularization φ K ρ
    (hkernel φ hφ hφc) (hgreen φ hφ hφc) (hdensity φ hφ hφc)

/-- Smooth radial regularization of the fundamental kernel.  Its Laplacian is
the approximate identity used by `apm_m95J02_weakIdentity_of_regularization`.
-/
def apm_m95J02_regularizedFundamental (n : ℕ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if n = 2 then
    Real.log (‖x‖ ^ 2 + ε ^ 2) / (4 * Real.pi)
  else
    -Real.rpow (‖x‖ ^ 2 + ε ^ 2) ((2 - (n : ℝ)) / 2) /
      (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

/-- A concrete nonzero value of the regularized kernel. -/
lemma apm_m95J02_regularizedFundamental_three_one_zero :
    apm_m95J02_regularizedFundamental 3 1
      (0 : EuclideanSpace ℝ (Fin 3)) =
        -1 / apm_m95J02_sphereArea 3 := by
  simp [apm_m95J02_regularizedFundamental]
  norm_num

lemma apm_m95J02_regularizedFundamental_three_one_zero_ne :
    apm_m95J02_regularizedFundamental 3 1
      (0 : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
  rw [apm_m95J02_regularizedFundamental_three_one_zero]
  exact div_ne_zero (by norm_num) (ne_of_gt (apm_m95J02_sphereArea_pos (by norm_num)))

lemma apm_m95J02_hasDerivAt_log_quadratic
    {A c s : ℝ} (hA : 0 < A) :
    HasDerivAt (fun u => c * Real.log (A + u ^ 2))
      (c * (2 * s / (A + s ^ 2))) s := by
  have hq : HasDerivAt (fun u : ℝ => A + u ^ 2) (2 * s) s := by
    convert (hasDerivAt_const s A).add (hasDerivAt_id s |>.pow 2) using 1
    all_goals simp [id, mul_comm]
  convert HasDerivAt.const_mul c (hq.log (by positivity)) using 1

lemma apm_m95J02_hasSecondDerivAt_log_quadratic
    {A c s : ℝ} (hA : 0 < A) :
    HasDerivAt
      (fun u => deriv (fun v => c * Real.log (A + v ^ 2)) u)
      (c * (2 * (A - s ^ 2) / (A + s ^ 2) ^ 2)) s := by
  have hfirst : (fun u => deriv (fun v => c * Real.log (A + v ^ 2)) u) =
      fun u => c * (2 * u / (A + u ^ 2)) := by
    funext u
    exact (apm_m95J02_hasDerivAt_log_quadratic (c := c) (s := u) hA).deriv
  rw [hfirst]
  have hn : HasDerivAt (fun u : ℝ => 2 * u) 2 s := by
    simpa [id] using HasDerivAt.const_mul 2 (hasDerivAt_id s)
  have hd : HasDerivAt (fun u : ℝ => A + u ^ 2) (2 * s) s := by
    convert (hasDerivAt_const s A).add (hasDerivAt_id s |>.pow 2) using 1
    all_goals simp [id, mul_comm]
  convert HasDerivAt.const_mul c (hn.div hd (by positivity)) using 1
  field_simp
  ring

lemma apm_m95J02_regularized_log_euler
    {ε r : ℝ} (hε : ε ≠ 0) (hr : r ≠ 0) :
    iteratedDeriv 2
        (fun s => Real.log (s ^ 2 + ε ^ 2) / (4 * Real.pi)) r +
      (1 / r) * deriv
        (fun s => Real.log (s ^ 2 + ε ^ 2) / (4 * Real.pi)) r =
      ε ^ 2 / (Real.pi * (r ^ 2 + ε ^ 2) ^ 2) := by
  let c : ℝ := 1 / (4 * Real.pi)
  have hA : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
  have hv : (fun s => Real.log (s ^ 2 + ε ^ 2) / (4 * Real.pi)) =
      fun s => c * Real.log (ε ^ 2 + s ^ 2) := by
    funext s
    dsimp [c]
    rw [add_comm]
    ring
  rw [hv, show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one]
  rw [(apm_m95J02_hasDerivAt_log_quadratic
    (A := ε ^ 2) (c := c) (s := r) hA).deriv]
  rw [(apm_m95J02_hasSecondDerivAt_log_quadratic
    (A := ε ^ 2) (c := c) (s := r) hA).deriv]
  have hden : ε ^ 2 + r ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  dsimp [c]
  field_simp
  ring

/-- First derivative of the regularized power profile.  This is kept in a
separate lemma so the radial Laplacian computation does not unfold `rpow`
inside the multivariable argument. -/
lemma apm_m95J02_hasDerivAt_regularized_rpow
    {A p s : ℝ} (hA : 0 < A) :
    HasDerivAt (fun u : ℝ => Real.rpow (u ^ 2 + A) p)
      (p * Real.rpow (s ^ 2 + A) (p - 1) * (2 * s)) s := by
  have hq : HasDerivAt (fun u : ℝ => u ^ 2 + A) (2 * s) s := by
    convert (hasDerivAt_id s |>.pow 2).add_const A using 1 <;> simp [id, mul_comm]
  convert (Real.hasDerivAt_rpow_const
      (p := p) (x := s ^ 2 + A) (Or.inl (ne_of_gt (by positivity)))).comp s hq using 1

/-- Second derivative of the regularized power profile. -/
lemma apm_m95J02_hasSecondDerivAt_regularized_rpow
    {A p s : ℝ} (hA : 0 < A) :
    HasDerivAt
      (fun u => deriv (fun v : ℝ => Real.rpow (v ^ 2 + A) p) u)
      (p * (p - 1) * Real.rpow (s ^ 2 + A) (p - 2) * (2 * s) ^ 2 +
        p * Real.rpow (s ^ 2 + A) (p - 1) * 2) s := by
  have hfirst :
      (fun u => deriv (fun v : ℝ => Real.rpow (v ^ 2 + A) p) u) =
        fun u => p * Real.rpow (u ^ 2 + A) (p - 1) * (2 * u) := by
    funext u
    exact (apm_m95J02_hasDerivAt_regularized_rpow
      (A := A) (p := p) (s := u) hA).deriv
  rw [hfirst]
  have hp := apm_m95J02_hasDerivAt_regularized_rpow
    (A := A) (p := p - 1) (s := s) hA
  have hs : HasDerivAt (fun u : ℝ => 2 * u) 2 s := by
    simpa [id] using HasDerivAt.const_mul 2 (hasDerivAt_id s)
  convert ((hp.const_mul p).mul hs) using 1 <;> ring

/-- The radial Euler operator applied to a regularized real power, expressed
without any exponent normalization.  The following normalization step can
therefore be proved purely with `Real.rpow_add` and field algebra. -/
lemma apm_m95J02_regularized_rpow_euler_raw
    {A p r m : ℝ} (hA : 0 < A) (hr : r ≠ 0) :
    iteratedDeriv 2 (fun s : ℝ => Real.rpow (s ^ 2 + A) p) r +
        ((m - 1) / r) *
          deriv (fun s : ℝ => Real.rpow (s ^ 2 + A) p) r =
      p * (p - 1) * Real.rpow (r ^ 2 + A) (p - 2) * (2 * r) ^ 2 +
        p * Real.rpow (r ^ 2 + A) (p - 1) * 2 +
        ((m - 1) / r) *
          (p * Real.rpow (r ^ 2 + A) (p - 1) * (2 * r)) := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one]
  rw [(apm_m95J02_hasDerivAt_regularized_rpow
    (A := A) (p := p) (s := r) hA).deriv]
  rw [(apm_m95J02_hasSecondDerivAt_regularized_rpow
    (A := A) (p := p) (s := r) hA).deriv]

/-- Algebraic normalization of the preceding Euler expression at the
fundamental-solution exponent. -/
lemma apm_m95J02_regularized_rpow_euler
    {A r : ℝ} {n : ℕ} (hA : 0 < A) (hr : r ≠ 0) :
    iteratedDeriv 2
        (fun s : ℝ => Real.rpow (s ^ 2 + A) ((2 - (n : ℝ)) / 2)) r +
      (((n : ℝ) - 1) / r) *
        deriv (fun s : ℝ =>
          Real.rpow (s ^ 2 + A) ((2 - (n : ℝ)) / 2)) r =
      ((2 - (n : ℝ)) / 2) * (n : ℝ) * A *
        Real.rpow (r ^ 2 + A) (((2 - (n : ℝ)) / 2) - 2) * 2 := by
  rw [apm_m95J02_regularized_rpow_euler_raw hA hr]
  have hq : 0 < r ^ 2 + A := by positivity
  have hp1 : Real.rpow (r ^ 2 + A) (((2 - (n : ℝ)) / 2) - 1) =
      Real.rpow (r ^ 2 + A) (((2 - (n : ℝ)) / 2) - 2) *
        (r ^ 2 + A) := by
    have he : ((2 - (n : ℝ)) / 2) - 1 =
        (((2 - (n : ℝ)) / 2) - 2) + 1 := by ring
    rw [he]
    exact Real.rpow_add_one hq.ne' _
  rw [hp1]
  field_simp
  ring

/-- One-variable profile of the regularized fundamental solution. -/
def apm_m95J02_regularizedProfile (n : ℕ) (ε r : ℝ) : ℝ :=
  if n = 2 then Real.log (r ^ 2 + ε ^ 2) / (4 * Real.pi)
  else
    -Real.rpow (r ^ 2 + ε ^ 2) ((2 - (n : ℝ)) / 2) /
      (((n : ℝ) - 2) * apm_m95J02_sphereArea n)

lemma apm_m95J02_regularizedProfile_three_one_zero :
    apm_m95J02_regularizedProfile 3 1 0 =
      -1 / apm_m95J02_sphereArea 3 := by
  simp [apm_m95J02_regularizedProfile]
  norm_num

lemma apm_m95J02_regularizedProfile_three_one_zero_ne :
    apm_m95J02_regularizedProfile 3 1 0 ≠ 0 := by
  rw [apm_m95J02_regularizedProfile_three_one_zero]
  exact div_ne_zero (by norm_num)
    (ne_of_gt (apm_m95J02_sphereArea_pos (by norm_num)))

lemma apm_m95J02_regularizedFundamental_eq_profile
    (n : ℕ) (ε : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    apm_m95J02_regularizedFundamental n ε x =
      apm_m95J02_regularizedProfile n ε ‖x‖ := by
  rfl

lemma apm_m95J02_regularizedProfile_contDiff_two
    (n : ℕ) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ 2 (apm_m95J02_regularizedProfile n ε) := by
  unfold apm_m95J02_regularizedProfile
  split_ifs
  · apply ContDiff.div_const
    apply ContDiff.log
    · fun_prop
    · intro r
      exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_ne_zero hε))
  · apply ContDiff.div_const
    apply ContDiff.neg
    rw [contDiff_iff_contDiffAt]
    intro r
    have hout : ContDiffAt ℝ 2
        (fun q : ℝ => Real.rpow q ((2 - (n : ℝ)) / 2)) (r ^ 2 + ε ^ 2) :=
      Real.contDiffAt_rpow_const (Or.inl (ne_of_gt
        (add_pos_of_nonneg_of_pos (sq_nonneg r) (sq_pos_of_ne_zero hε))))
    have hin : ContDiffAt ℝ 2 (fun s : ℝ => s ^ 2 + ε ^ 2) r := by
      fun_prop
    convert hout.comp r hin using 1

lemma apm_m95J02_laplacian_regularizedFundamental_two
    {ε : ℝ} (hε : ε ≠ 0) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    Laplacian.laplacian (apm_m95J02_regularizedFundamental 2 ε) x =
      ε ^ 2 / (Real.pi * (‖x‖ ^ 2 + ε ^ 2) ^ 2) := by
  rw [show apm_m95J02_regularizedFundamental 2 ε =
      fun z : EuclideanSpace ℝ (Fin 2) =>
        apm_m95J02_regularizedProfile 2 ε ‖z‖ by
    funext z
    exact apm_m95J02_regularizedFundamental_eq_profile 2 ε z]
  rw [apm_m95J02_laplacian_radial
    (apm_m95J02_regularizedProfile 2 ε) x
    (apm_m95J02_regularizedProfile_contDiff_two 2 hε).contDiffAt hx]
  rw [show apm_m95J02_regularizedProfile 2 ε =
      fun s => Real.log (s ^ 2 + ε ^ 2) / (4 * Real.pi) by
    funext s
    simp [apm_m95J02_regularizedProfile]]
  convert (apm_m95J02_regularized_log_euler (hε := hε)
      (hr := norm_ne_zero_iff.mpr hx)) using 1 <;> norm_num

lemma apm_m95J02_regularizedProfile_euler_of_two_lt
    {n : ℕ} (hn : 2 < n) {ε r : ℝ} (hε : ε ≠ 0) (hr : r ≠ 0) :
    iteratedDeriv 2 (apm_m95J02_regularizedProfile n ε) r +
        (((n : ℝ) - 1) / r) *
          deriv (apm_m95J02_regularizedProfile n ε) r =
      (n : ℝ) * ε ^ 2 / apm_m95J02_sphereArea n *
        Real.rpow (r ^ 2 + ε ^ 2) (((2 - (n : ℝ)) / 2) - 2) := by
  rw [show apm_m95J02_regularizedProfile n ε = fun s =>
      -Real.rpow (s ^ 2 + ε ^ 2) ((2 - (n : ℝ)) / 2) /
        (((n : ℝ) - 2) * apm_m95J02_sphereArea n) by
    funext s
    simp [apm_m95J02_regularizedProfile, show n ≠ 2 by omega]]
  simp only [iteratedDeriv_div_const, iteratedDeriv_fun_neg, deriv_div_const,
    deriv.fun_neg]
  have he := apm_m95J02_regularized_rpow_euler
    (n := n) (A := ε ^ 2) (r := r) (sq_pos_of_ne_zero hε) hr
  have hnR : (n : ℝ) - 2 ≠ 0 := by exact sub_ne_zero.mpr (by exact_mod_cast (show n ≠ 2 by omega))
  have hw : apm_m95J02_sphereArea n ≠ 0 :=
    ne_of_gt (apm_m95J02_sphereArea_pos (by omega))
  have hs := congrArg (fun z : ℝ =>
    -z / (((n : ℝ) - 2) * apm_m95J02_sphereArea n)) he
  convert hs using 1 <;> field_simp [hnR, hw] <;> ring

lemma apm_m95J02_laplacian_regularizedFundamental_of_two_lt
    {n : ℕ} (hn : 2 < n) {ε : ℝ} (hε : ε ≠ 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    Laplacian.laplacian (apm_m95J02_regularizedFundamental n ε) x =
      (n : ℝ) * ε ^ 2 / apm_m95J02_sphereArea n *
        Real.rpow (‖x‖ ^ 2 + ε ^ 2) (((2 - (n : ℝ)) / 2) - 2) := by
  rw [show apm_m95J02_regularizedFundamental n ε =
      fun z : EuclideanSpace ℝ (Fin n) =>
        apm_m95J02_regularizedProfile n ε ‖z‖ by
    funext z
    exact apm_m95J02_regularizedFundamental_eq_profile n ε z]
  rw [apm_m95J02_laplacian_radial
    (apm_m95J02_regularizedProfile n ε) x
    (apm_m95J02_regularizedProfile_contDiff_two n hε).contDiffAt hx]
  exact apm_m95J02_regularizedProfile_euler_of_two_lt hn hε
    (norm_ne_zero_iff.mpr hx)

/-- The regularized kernel is smooth even at the origin.  The proof goes
through the squared norm, avoiding the nondifferentiability of the norm
itself at zero. -/
lemma apm_m95J02_regularizedFundamental_contDiff
    (n : ℕ) {ε : ℝ} (hε : ε ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (apm_m95J02_regularizedFundamental n ε) := by
  unfold apm_m95J02_regularizedFundamental
  split_ifs
  · apply ContDiff.div_const
    apply ContDiff.log ((contDiff_norm_sq ℝ).add contDiff_const)
    intro x
    exact ne_of_gt
      (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (sq_pos_of_ne_zero hε))
  · apply ContDiff.div_const
    apply ContDiff.neg
    rw [contDiff_iff_contDiffAt]
    intro x
    have hout : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ => Real.rpow q ((2 - (n : ℝ)) / 2))
        (‖x‖ ^ 2 + ε ^ 2) :=
      Real.contDiffAt_rpow_const_of_ne (ne_of_gt
        (add_pos_of_nonneg_of_pos (sq_nonneg ‖x‖) (sq_pos_of_ne_zero hε)))
    have hin : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2 + ε ^ 2) x :=
      ((contDiff_norm_sq ℝ).add contDiff_const).contDiffAt
    convert hout.comp x hin using 1

lemma apm_m95J02_contDiff_directional_fderiv
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (v : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ f x v) := by
  exact (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma apm_m95J02_directional_fderiv_hasCompactSupport
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HasCompactSupport f) (v : EuclideanSpace ℝ (Fin n)) :
    HasCompactSupport (fun x => fderiv ℝ f x v) := by
  apply (hf.fderiv ℝ).mono
  intro x hx hzero
  exact hx (by simpa using congrArg (fun L => L v) hzero)

lemma apm_m95J02_continuous_mul_integrable
    {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => f x * g x) volume := by
  exact (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

/-- Two integrations by parts in an arbitrary Euclidean direction. -/
lemma apm_m95J02_integral_mul_second_directional_eq
    {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) (v : EuclideanSpace ℝ (Fin n)) :
    (∫ x, f x * fderiv ℝ (fun q => fderiv ℝ g q v) x v) =
      ∫ x, fderiv ℝ (fun q => fderiv ℝ f q v) x v * g x := by
  let df : EuclideanSpace ℝ (Fin n) → ℝ := fun x => fderiv ℝ f x v
  let dg : EuclideanSpace ℝ (Fin n) → ℝ := fun x => fderiv ℝ g x v
  have hdf := apm_m95J02_contDiff_directional_fderiv f hf v
  have hdg := apm_m95J02_contDiff_directional_fderiv g hg v
  have hddf := apm_m95J02_contDiff_directional_fderiv df hdf v
  have hddg := apm_m95J02_contDiff_directional_fderiv dg hdg v
  have hdgc := apm_m95J02_directional_fderiv_hasCompactSupport g hgc v
  have hfg : Integrable (fun x => f x * g x) volume :=
    apm_m95J02_continuous_mul_integrable f g hf.continuous hg.continuous hgc
  have hfdg : Integrable (fun x => f x * dg x) volume :=
    apm_m95J02_continuous_mul_integrable f dg hf.continuous hdg.continuous hdgc
  have hdfg : Integrable (fun x => df x * g x) volume :=
    apm_m95J02_continuous_mul_integrable df g hdf.continuous hg.continuous hgc
  have hdfdg : Integrable (fun x => df x * dg x) volume :=
    apm_m95J02_continuous_mul_integrable df dg hdf.continuous hdg.continuous hdgc
  have hfddg : Integrable (fun x => f x * fderiv ℝ dg x v) volume :=
    apm_m95J02_continuous_mul_integrable f _ hf.continuous hddg.continuous
      (apm_m95J02_directional_fderiv_hasCompactSupport dg hdgc v)
  have hddfg : Integrable (fun x => fderiv ℝ df x v * g x) volume :=
    apm_m95J02_continuous_mul_integrable _ g hddf.continuous hg.continuous hgc
  have hfirst := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := dg) (v := v) hdfdg hfddg hfdg
    (fun _ _ => (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ => (hdg.differentiable (by simp)).differentiableAt)
  have hsecond := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := df) (g := g) (v := v) hddfg hdfdg hdfg
    (fun _ _ => (hdf.differentiable (by simp)).differentiableAt)
    (fun _ _ => (hg.differentiable (by simp)).differentiableAt)
  dsimp [df, dg] at hfirst hsecond ⊢
  rw [hfirst, hsecond]
  simp

lemma apm_m95J02_second_directional_eq_iteratedFDeriv
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun q => fderiv ℝ f q v) x v =
      iteratedFDeriv ℝ 2 f x ![v, v] := by
  have hfd : Differentiable ℝ (fderiv ℝ f) :=
    (contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)
  rw [fderiv_clm_apply hfd.differentiableAt
    (differentiable_const _).differentiableAt]
  simp [iteratedFDeriv_two_apply]

/-- Self-adjointness of the Euclidean Laplacian when the right factor is a
smooth compactly supported test function, in arbitrary finite dimension. -/
lemma apm_m95J02_integral_mul_laplacian_eq
    {n : ℕ} (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hgc : HasCompactSupport g) :
    (∫ x, f x * Laplacian.laplacian g x) =
      ∫ x, Laplacian.laplacian f x * g x := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hleft (i : Fin n) : Integrable
      (fun x => f x * fderiv ℝ (fun q => fderiv ℝ g q (b i)) x (b i)) volume := by
    apply apm_m95J02_continuous_mul_integrable f _ hf.continuous
    · exact (apm_m95J02_contDiff_directional_fderiv _
        (apm_m95J02_contDiff_directional_fderiv g hg (b i)) (b i)).continuous
    · exact apm_m95J02_directional_fderiv_hasCompactSupport _
        (apm_m95J02_directional_fderiv_hasCompactSupport g hgc (b i)) (b i)
  have hright (i : Fin n) : Integrable
      (fun x => fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x) volume := by
    apply apm_m95J02_continuous_mul_integrable _ g
    · exact (apm_m95J02_contDiff_directional_fderiv _
        (apm_m95J02_contDiff_directional_fderiv f hf (b i)) (b i)).continuous
    · exact hg.continuous
    · exact hgc
  calc
    (∫ x, f x * Laplacian.laplacian g x) =
        ∫ x, ∑ i : Fin n,
          f x * fderiv ℝ (fun q => fderiv ℝ g q (b i)) x (b i) := by
      congr 1
      funext x
      calc
        f x * Laplacian.laplacian g x =
            f x * ∑ i : Fin n, iteratedFDeriv ℝ 2 g x ![b i, b i] :=
          congrArg (fun z => f x * z)
            (congrFun
              (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g b) x)
        _ = _ := by
          simp_rw [← apm_m95J02_second_directional_eq_iteratedFDeriv g hg]
          rw [Finset.mul_sum]
    _ = ∑ i : Fin n, ∫ x,
          f x * fderiv ℝ (fun q => fderiv ℝ g q (b i)) x (b i) := by
      exact MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hleft i)
    _ = ∑ i : Fin n, ∫ x,
          fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x := by
      apply Finset.sum_congr rfl
      intro i _
      exact apm_m95J02_integral_mul_second_directional_eq f g hf hg hgc (b i)
    _ = ∫ x, ∑ i : Fin n,
          fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x := by
      symm
      exact MeasureTheory.integral_finset_sum Finset.univ (fun i _ => hright i)
    _ = ∫ x, Laplacian.laplacian f x * g x := by
      congr 1
      funext x
      calc
        (∑ i : Fin n,
            fderiv ℝ (fun q => fderiv ℝ f q (b i)) x (b i) * g x) =
            (∑ i : Fin n, iteratedFDeriv ℝ 2 f x ![b i, b i]) * g x := by
          simp_rw [← apm_m95J02_second_directional_eq_iteratedFDeriv f hf]
          rw [Finset.sum_mul]
        _ = Laplacian.laplacian f x * g x :=
          congrArg (fun z => z * g x)
            (congrFun
              (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f b) x).symm

lemma apm_m95J02_regularizedFundamental_green_identity
    {n : ℕ} {ε : ℝ} (hε : ε ≠ 0)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, apm_m95J02_regularizedFundamental n ε x *
        Laplacian.laplacian φ x) =
      ∫ x, Laplacian.laplacian
        (apm_m95J02_regularizedFundamental n ε) x * φ x := by
  exact apm_m95J02_integral_mul_laplacian_eq
    (apm_m95J02_regularizedFundamental n ε) φ
    (apm_m95J02_regularizedFundamental_contDiff n hε) hφ hφc

lemma apm_m95J02_regularizedFundamental_tendsto
    {n : ℕ} {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0) :
    Filter.Tendsto (fun ε : ℝ => apm_m95J02_regularizedFundamental n ε x)
      (nhds 0) (nhds (apm_m95J02_fundamental n x)) := by
  have hnorm : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have harg : Filter.Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2)
      (nhds 0) (nhds (‖x‖ ^ 2)) := by
    have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhds 0) (nhds 0) :=
      Filter.tendsto_id
    convert tendsto_const_nhds.add (hid.pow 2) using 1 <;> norm_num
  by_cases hn2 : n = 2
  · subst n
    have hlog := (Real.continuousAt_log hnorm).tendsto.comp harg
    have ht := hlog.div_const (4 * Real.pi)
    convert ht using 1
    rw [apm_m95J02_fundamental]
    simp only [if_pos]
    rw [Real.log_pow]
    ring
  · have hp0 : ContinuousAt
        (fun q : ℝ => Real.rpow q ((2 - (n : ℝ)) / 2)) (‖x‖ ^ 2) :=
      (Real.contDiffAt_rpow_const_of_ne
        (p := (2 - (n : ℝ)) / 2) (n := (0 : WithTop ℕ∞)) hnorm).continuousAt
    have hp := hp0.tendsto.comp harg
    have ht := hp.neg.div_const
      (((n : ℝ) - 2) * apm_m95J02_sphereArea n)
    have hpow : Real.rpow (‖x‖ ^ 2) ((2 - (n : ℝ)) / 2) =
        Real.rpow ‖x‖ (2 - (n : ℝ)) := by
      calc
        _ = Real.rpow ‖x‖ ((2 : ℝ) * ((2 - (n : ℝ)) / 2)) :=
          (Real.rpow_natCast_mul (norm_nonneg x) 2
            ((2 - (n : ℝ)) / 2)).symm
        _ = _ := by congr 1 <;> ring
    convert ht using 1
    · funext ε
      simp [apm_m95J02_regularizedFundamental, hn2]
    · rw [apm_m95J02_fundamental, if_neg hn2, hpow]

lemma apm_m95J02_regularized_rpow_le_singular
    {n : ℕ} (hn : 2 < n) {r ε : ℝ} (hr : 0 < r) :
    Real.rpow (r ^ 2 + ε ^ 2) ((2 - (n : ℝ)) / 2) ≤
      Real.rpow r (2 - (n : ℝ)) := by
  have hp : (2 - (n : ℝ)) / 2 ≤ 0 := by
    have : (2 : ℝ) < n := by exact_mod_cast hn
    linarith
  have hbase : r ^ 2 ≤ r ^ 2 + ε ^ 2 := le_add_of_nonneg_right (sq_nonneg ε)
  have hle := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hr) hbase hp
  calc
    Real.rpow (r ^ 2 + ε ^ 2) ((2 - (n : ℝ)) / 2) ≤
        Real.rpow (r ^ 2) ((2 - (n : ℝ)) / 2) := hle
    _ = Real.rpow r (2 - (n : ℝ)) := by
      calc
        _ = Real.rpow r ((2 : ℝ) * ((2 - (n : ℝ)) / 2)) :=
          (Real.rpow_natCast_mul hr.le 2 ((2 - (n : ℝ)) / 2)).symm
        _ = _ := by congr 1 <;> ring

lemma apm_m95J02_regularizedFundamental_abs_le_of_two_lt
    {n : ℕ} (hn : 2 < n) {ε : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ≠ 0) :
    |apm_m95J02_regularizedFundamental n ε x| ≤
      |apm_m95J02_fundamental n x| := by
  have hD : 0 < ((n : ℝ) - 2) * apm_m95J02_sphereArea n :=
    apm_m95J02_power_denominator_pos hn
  have hreg_nonpos : apm_m95J02_regularizedFundamental n ε x ≤ 0 := by
    rw [apm_m95J02_regularizedFundamental, if_neg (by omega)]
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (Real.rpow_nonneg (by positivity) _)) hD.le
  have hfund_nonpos : apm_m95J02_fundamental n x ≤ 0 :=
    (apm_m95J02_fundamental_neg hn hx).le
  rw [abs_of_nonpos hreg_nonpos, abs_of_nonpos hfund_nonpos]
  rw [apm_m95J02_regularizedFundamental, if_neg (by omega)]
  rw [apm_m95J02_fundamental, if_neg (by omega)]
  have hp := apm_m95J02_regularized_rpow_le_singular hn
    (r := ‖x‖) (ε := ε) (norm_pos_iff.mpr hx)
  have hdiv := (div_le_div_iff_of_pos_right hD).mpr hp
  simpa only [neg_div, neg_neg] using hdiv

lemma apm_m95J02_hasDerivAt_radial_mass_primitive_raw
    (n : ℕ) (r : ℝ) :
    HasDerivAt
      (fun s : ℝ => s ^ n * Real.rpow (s ^ 2 + 1) (-(n : ℝ) / 2))
      ((n : ℝ) * r ^ (n - 1) * Real.rpow (r ^ 2 + 1) (-(n : ℝ) / 2) +
        r ^ n * ((-(n : ℝ) / 2) *
          Real.rpow (r ^ 2 + 1) ((-(n : ℝ) / 2) - 1) * (2 * r))) r := by
  have hp : HasDerivAt (fun s : ℝ => s ^ n) ((n : ℝ) * r ^ (n - 1)) r := by
    simpa [id] using (hasDerivAt_id r).pow n
  have hq := apm_m95J02_hasDerivAt_regularized_rpow
    (A := (1 : ℝ)) (p := -(n : ℝ) / 2) (s := r) (by norm_num)
  simpa only [Pi.mul_apply] using hp.mul hq

lemma apm_m95J02_hasDerivAt_radial_mass_primitive
    {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun s : ℝ => s ^ n * Real.rpow (s ^ 2 + 1) (-(n : ℝ) / 2))
      ((n : ℝ) * r ^ (n - 1) *
        Real.rpow (r ^ 2 + 1) (-((n : ℝ) + 2) / 2)) r := by
  have hraw := apm_m95J02_hasDerivAt_radial_mass_primitive_raw n r
  convert hraw using 1
  have hq : 0 < r ^ 2 + 1 := by positivity
  have hshift : Real.rpow (r ^ 2 + 1) (-(n : ℝ) / 2) =
      Real.rpow (r ^ 2 + 1) (-((n : ℝ) + 2) / 2) * (r ^ 2 + 1) := by
    have he : -(n : ℝ) / 2 = -((n : ℝ) + 2) / 2 + 1 := by ring
    rw [he]
    exact Real.rpow_add_one hq.ne' _
  have hrpow : r ^ n = r ^ (n - 1) * r := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  rw [hshift, hrpow]
  ring

lemma apm_m95J02_hasDerivAt_radial_mass_primitive_nonneg
    {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt
      (fun s : ℝ => s ^ n * Real.rpow (s ^ 2 + 1) (-(n : ℝ) / 2))
      ((n : ℝ) * r ^ (n - 1) *
        Real.rpow (r ^ 2 + 1) (-((n : ℝ) + 2) / 2)) r := by
  rcases hr.eq_or_lt with rfl | hr
  · have hraw := apm_m95J02_hasDerivAt_radial_mass_primitive_raw n 0
    simpa [show n - 1 ≠ 0 by omega] using hraw
  · exact apm_m95J02_hasDerivAt_radial_mass_primitive (by omega) hr

lemma apm_m95J02_tendsto_radial_mass_primitive (n : ℕ) :
    Filter.Tendsto
      (fun r : ℝ => r ^ n * Real.rpow (r ^ 2 + 1) (-(n : ℝ) / 2))
      Filter.atTop (nhds 1) := by
  have hsq : Filter.Tendsto (fun r : ℝ => r ^ 2)
      Filter.atTop Filter.atTop := by
    simpa [pow_two] using
      (Filter.tendsto_id : Filter.Tendsto (fun r : ℝ => r)
        Filter.atTop Filter.atTop).atTop_mul_atTop₀ Filter.tendsto_id
  have hden : Filter.Tendsto (fun r : ℝ => r ^ 2 + 1)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 hsq
  have hinv : Filter.Tendsto (fun r : ℝ => 1 / (r ^ 2 + 1))
      Filter.atTop (nhds 0) := hden.const_div_atTop 1
  have hratio : Filter.Tendsto (fun r : ℝ => r ^ 2 / (r ^ 2 + 1))
      Filter.atTop (nhds 1) := by
    have h : Filter.Tendsto (fun r : ℝ => (1 : ℝ) - 1 / (r ^ 2 + 1))
        Filter.atTop (nhds (1 : ℝ)) :=
      by
        convert (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          Filter.atTop (nhds 1)).sub hinv using 1 <;> norm_num
    apply h.congr'
    filter_upwards [] with r
    field_simp
    ring
  have hpow : Filter.Tendsto
      (fun r : ℝ => Real.rpow (r ^ 2 / (r ^ 2 + 1)) ((n : ℝ) / 2))
      Filter.atTop (nhds 1) := by
    have hc : ContinuousAt (fun q : ℝ => Real.rpow q ((n : ℝ) / 2)) 1 :=
      (Real.contDiffAt_rpow_const_of_ne
        (p := (n : ℝ) / 2) (n := (0 : WithTop ℕ∞)) one_ne_zero).continuousAt
    simpa using hc.tendsto.comp hratio
  apply hpow.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with r hr
  have hq : 0 ≤ r ^ 2 + 1 := by positivity
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hdiv : Real.rpow (r ^ 2 / (r ^ 2 + 1)) ((n : ℝ) / 2) =
      Real.rpow (r ^ 2) ((n : ℝ) / 2) /
        Real.rpow (r ^ 2 + 1) ((n : ℝ) / 2) :=
    Real.div_rpow hr2 hq _
  rw [hdiv]
  have hneg : Real.rpow (r ^ 2 + 1) (-((n : ℝ) / 2)) =
      (Real.rpow (r ^ 2 + 1) ((n : ℝ) / 2))⁻¹ :=
    Real.rpow_neg hq _
  have hneg' : Real.rpow (r ^ 2 + 1) (-(n : ℝ) / 2) =
      (Real.rpow (r ^ 2 + 1) ((n : ℝ) / 2))⁻¹ := by
    convert hneg using 1 <;> ring
  have hrpow : Real.rpow (r ^ 2) ((n : ℝ) / 2) = r ^ n := by
    calc
      _ = Real.rpow r ((2 : ℝ) * ((n : ℝ) / 2)) :=
        (Real.rpow_natCast_mul hr.le 2 ((n : ℝ) / 2)).symm
      _ = _ := by
        rw [show (2 : ℝ) * ((n : ℝ) / 2) = n by ring]
        exact Real.rpow_natCast r n
  rw [hrpow]
  rw [hneg']
  simp [div_eq_mul_inv, Real.rpow_natCast]

lemma apm_m95J02_radial_mass_integral_unscaled
    {n : ℕ} (hn : 2 ≤ n) :
    (∫ r in Set.Ioi (0 : ℝ),
      (n : ℝ) * r ^ (n - 1) *
        Real.rpow (r ^ 2 + 1) (-((n : ℝ) + 2) / 2)) = 1 := by
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun r : ℝ => r ^ n * Real.rpow (r ^ 2 + 1) (-(n : ℝ) / 2))
    (g' := fun r : ℝ => (n : ℝ) * r ^ (n - 1) *
      Real.rpow (r ^ 2 + 1) (-((n : ℝ) + 2) / 2))
    (a := 0) (l := 1)
    (fun r hr => apm_m95J02_hasDerivAt_radial_mass_primitive_nonneg hn hr)
    (fun r hr => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.le _))
      (Real.rpow_nonneg (by positivity) _))
    (apm_m95J02_tendsto_radial_mass_primitive n)
  simpa [show n ≠ 0 by omega] using h

lemma apm_m95J02_radial_peak_integral
    {n : ℕ} (hn : 2 ≤ n) :
    (∫ r in Set.Ioi (0 : ℝ),
      r ^ (n - 1) * ((n : ℝ) / apm_m95J02_sphereArea n) *
        Real.rpow (1 + r ^ 2) (-((n : ℝ) + 2) / 2)) =
      1 / apm_m95J02_sphereArea n := by
  have hmass := apm_m95J02_radial_mass_integral_unscaled hn
  calc
    _ = (1 / apm_m95J02_sphereArea n) *
        ∫ r in Set.Ioi (0 : ℝ),
          (n : ℝ) * r ^ (n - 1) *
            Real.rpow (r ^ 2 + 1) (-((n : ℝ) + 2) / 2) := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with r
      ring
    _ = _ := by rw [hmass]; ring

noncomputable def apm_m95J02_peakProfile (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (n : ℝ) / apm_m95J02_sphereArea n *
    Real.rpow (1 + ‖x‖ ^ 2) (-((n : ℝ) + 2) / 2)

lemma apm_m95J02_peakProfile_two_zero :
    apm_m95J02_peakProfile 2 (0 : EuclideanSpace ℝ (Fin 2)) =
      1 / Real.pi := by
  simp [apm_m95J02_peakProfile, apm_m95J02_sphereArea_two]
  ring

lemma apm_m95J02_peakProfile_nonneg {n : ℕ} (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ apm_m95J02_peakProfile n x := by
  unfold apm_m95J02_peakProfile
  exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (apm_m95J02_sphereArea_pos hn).le)
    (Real.rpow_nonneg (by positivity) _)

lemma apm_m95J02_peakProfile_integral {n : ℕ} (hn : 2 ≤ n) :
    ∫ x : EuclideanSpace ℝ (Fin n), apm_m95J02_peakProfile n x = 1 := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  change (∫ x : EuclideanSpace ℝ (Fin n),
    (fun r : ℝ => (n : ℝ) / apm_m95J02_sphereArea n *
      Real.rpow (1 + r ^ 2) (-((n : ℝ) + 2) / 2)) ‖x‖) = 1
  calc
    _ = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) •
        (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) •
        ∫ r in Set.Ioi (0 : ℝ), r ^ (Module.finrank ℝ
          (EuclideanSpace ℝ (Fin n)) - 1) •
          ((n : ℝ) / apm_m95J02_sphereArea n *
            Real.rpow (1 + r ^ 2) (-((n : ℝ) + 2) / 2)) :=
      MeasureTheory.integral_fun_norm_addHaar
        (volume : Measure (EuclideanSpace ℝ (Fin n))) _
    _ = 1 := by
      simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
      have hrad := apm_m95J02_radial_peak_integral hn
      rw [show (∫ r in Set.Ioi (0 : ℝ),
          r ^ (n - 1) * ((n : ℝ) / apm_m95J02_sphereArea n *
            Real.rpow (1 + r ^ 2) (-((n : ℝ) + 2) / 2))) =
          1 / apm_m95J02_sphereArea n by
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hrad]
      simp only [nsmul_eq_mul]
      rw [← mul_assoc]
      have hs := apm_m95J02_finrank_volume_unitBall_mul_eq_sphereArea n
      simp only [finrank_euclideanSpace, Fintype.card_fin] at hs
      rw [hs]
      simpa [div_eq_mul_inv] using div_self (ne_of_gt
        (apm_m95J02_sphereArea_pos (show 0 < n by omega)))

lemma apm_m95J02_peakProfile_integrable {n : ℕ} (hn : 2 ≤ n) :
    Integrable (apm_m95J02_peakProfile n) volume :=
  integrable_of_integral_eq_one (apm_m95J02_peakProfile_integral hn)

lemma apm_m95J02_tendsto_radial_peak_weighted_zero (n : ℕ) :
    Filter.Tendsto
      (fun r : ℝ => r ^ n *
        Real.rpow (1 + r ^ 2) (-((n : ℝ) + 2) / 2))
      Filter.atTop (nhds 0) := by
  have hden : Filter.Tendsto (fun r : ℝ => 1 + r ^ 2)
      Filter.atTop Filter.atTop := by
    have hsq : Filter.Tendsto (fun r : ℝ => r ^ 2)
        Filter.atTop Filter.atTop := by
      simpa [pow_two] using
        (Filter.tendsto_id : Filter.Tendsto (fun r : ℝ => r)
          Filter.atTop Filter.atTop).atTop_mul_atTop₀ Filter.tendsto_id
    simpa [add_comm] using
      Filter.tendsto_atTop_add_const_right Filter.atTop 1 hsq
  have hinv : Filter.Tendsto (fun r : ℝ => 1 / (1 + r ^ 2))
      Filter.atTop (nhds 0) := hden.const_div_atTop 1
  have hmul := (apm_m95J02_tendsto_radial_mass_primitive n).mul hinv
  have hmul0 : Filter.Tendsto
      (fun r : ℝ => (r ^ n * Real.rpow (r ^ 2 + 1) (-(n : ℝ) / 2)) *
        (1 / (1 + r ^ 2))) Filter.atTop (nhds 0) := by
    simpa using hmul
  apply hmul0.congr'
  filter_upwards [] with r
  have hq : 0 < 1 + r ^ 2 := by positivity
  have hshift : Real.rpow (1 + r ^ 2) (-((n : ℝ) + 2) / 2) =
      Real.rpow (1 + r ^ 2) (-(n : ℝ) / 2) * (1 + r ^ 2)⁻¹ := by
    have he : -((n : ℝ) + 2) / 2 = -(n : ℝ) / 2 - 1 := by ring
    rw [he]
    simpa [div_eq_mul_inv] using
      (Real.rpow_sub_one hq.ne' (-(n : ℝ) / 2))
  calc
    r ^ n * Real.rpow (r ^ 2 + 1) (-(n : ℝ) / 2) *
        (1 / (1 + r ^ 2)) =
      r ^ n * (Real.rpow (1 + r ^ 2) (-(n : ℝ) / 2) *
        (1 + r ^ 2)⁻¹) := by ring
    _ = _ := by rw [← hshift]

lemma apm_m95J02_peakProfile_weighted_tendsto
    {n : ℕ} (hn : 2 ≤ n) :
    Filter.Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖x‖ ^ n * apm_m95J02_peakProfile n x)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (nhds 0) := by
  have hs := (apm_m95J02_tendsto_radial_peak_weighted_zero n).const_mul
    ((n : ℝ) / apm_m95J02_sphereArea n)
  have ht := hs.comp (tendsto_norm_cocompact_atTop
    (E := EuclideanSpace ℝ (Fin n)))
  have ht0 : Filter.Tendsto
      ((fun r : ℝ => (n : ℝ) / apm_m95J02_sphereArea n *
        (r ^ n * Real.rpow (1 + r ^ 2) (-((n : ℝ) + 2) / 2))) ∘ norm)
      (Filter.cocompact (EuclideanSpace ℝ (Fin n))) (nhds 0) := by
    simpa using ht
  rw [Metric.cobounded_eq_cocompact]
  apply ht0.congr'
  filter_upwards [] with x
  simp only [Function.comp_apply, apm_m95J02_peakProfile]
  ring

set_option maxHeartbeats 800000 in
lemma apm_m95J02_peakProfile_tendsto_integral
    {n : ℕ} (hn : 2 ≤ n)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (y : EuclideanSpace ℝ (Fin n))
    (hφi : Integrable φ volume) (hφy : ContinuousAt φ y) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        (c ^ n * apm_m95J02_peakProfile n (c • (y - x))) * φ x)
      Filter.atTop (nhds (φ y)) := by
  have hdecay : Filter.Tendsto
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ‖x‖ ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) *
          apm_m95J02_peakProfile n x)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (nhds 0) := by
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      apm_m95J02_peakProfile_weighted_tendsto hn
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using
    (tendsto_integral_comp_smul_smul_of_integrable'
      (apm_m95J02_peakProfile_nonneg (show 0 < n by omega))
      (apm_m95J02_peakProfile_integral hn) hdecay hφi hφy)

lemma apm_m95J02_peakProfile_scale_two
    {c : ℝ} (hc : 0 < c) (x : EuclideanSpace ℝ (Fin 2)) :
    c ^ 2 * apm_m95J02_peakProfile 2 (c • (-x)) =
      (c⁻¹) ^ 2 / (Real.pi * (‖x‖ ^ 2 + (c⁻¹) ^ 2) ^ 2) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  rw [apm_m95J02_peakProfile, apm_m95J02_sphereArea_two,
    norm_smul, Real.norm_eq_abs, abs_of_pos hc, norm_neg]
  norm_num
  field_simp
  ring

lemma apm_m95J02_regularized_density_tendsto_two
    (φ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        Laplacian.laplacian
          (apm_m95J02_regularizedFundamental 2 c⁻¹) x * φ x)
      Filter.atTop (nhds (φ 0)) := by
  have hpeak := apm_m95J02_peakProfile_tendsto_integral
    (n := 2) (by omega) φ 0
    (hφ.integrable_of_hasCompactSupport hφc) hφ.continuousAt
  apply hpeak.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
  apply MeasureTheory.integral_congr_ae
  filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin 2))).ae_ne
    (0 : EuclideanSpace ℝ (Fin 2))] with x hx
  rw [apm_m95J02_laplacian_regularizedFundamental_two
    (inv_ne_zero (ne_of_gt hc)) hx]
  rw [← apm_m95J02_peakProfile_scale_two hc x]
  simp

lemma apm_m95J02_peakProfile_scale_of_two_lt
    {n : ℕ} (hn : 2 < n) {c : ℝ} (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin n)) :
    c ^ n * apm_m95J02_peakProfile n (c • (-x)) =
      (n : ℝ) * (c⁻¹) ^ 2 / apm_m95J02_sphereArea n *
        Real.rpow (‖x‖ ^ 2 + (c⁻¹) ^ 2)
          (((2 - (n : ℝ)) / 2) - 2) := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  let a : ℝ := -((n : ℝ) + 2) / 2
  have ha : ((2 - (n : ℝ)) / 2) - 2 = a := by
    dsimp [a]
    ring
  have hbase : ‖x‖ ^ 2 + (c⁻¹) ^ 2 =
      (1 + (c * ‖x‖) ^ 2) / c ^ 2 := by
    field_simp
    ring
  have hpowc : Real.rpow (c ^ 2) a = (c ^ (n + 2))⁻¹ := by
    have h := Real.rpow_natCast_mul hc.le 2 a
    norm_num at h
    rw [show (2 : ℝ) * a = -((n : ℝ) + 2) by
      dsimp [a]; ring] at h
    rw [Real.rpow_neg hc.le] at h
    have hn2 : (n : ℝ) + 2 = ((n + 2 : ℕ) : ℝ) := by norm_num
    rw [hn2, Real.rpow_natCast] at h
    exact h.symm
  rw [apm_m95J02_peakProfile, norm_smul, Real.norm_eq_abs,
    abs_of_pos hc, norm_neg, ha, hbase]
  change c ^ n * ((n : ℝ) / apm_m95J02_sphereArea n *
      Real.rpow (1 + (c * ‖x‖) ^ 2) a) =
    (n : ℝ) * (c⁻¹) ^ 2 / apm_m95J02_sphereArea n *
      Real.rpow ((1 + (c * ‖x‖) ^ 2) / c ^ 2) a
  have hdiv : Real.rpow ((1 + (c * ‖x‖) ^ 2) / c ^ 2) a =
      Real.rpow (1 + (c * ‖x‖) ^ 2) a / Real.rpow (c ^ 2) a := by
    exact Real.div_rpow
      (show 0 ≤ 1 + (c * ‖x‖) ^ 2 by positivity) hc2.le a
  calc
    c ^ n * ((n : ℝ) / apm_m95J02_sphereArea n *
        Real.rpow (1 + (c * ‖x‖) ^ 2) a) =
      (n : ℝ) * (c⁻¹) ^ 2 / apm_m95J02_sphereArea n *
        (Real.rpow (1 + (c * ‖x‖) ^ 2) a /
          Real.rpow (c ^ 2) a) := by
            rw [hpowc]
            field_simp
            ring
    _ = _ := by rw [← hdiv]

lemma apm_m95J02_regularized_density_tendsto_of_two_lt
    {n : ℕ} (hn : 2 < n)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        Laplacian.laplacian
          (apm_m95J02_regularizedFundamental n c⁻¹) x * φ x)
      Filter.atTop (nhds (φ 0)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hpeak := apm_m95J02_peakProfile_tendsto_integral
    (n := n) (by omega) φ 0
    (hφ.integrable_of_hasCompactSupport hφc) hφ.continuousAt
  apply hpeak.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with c hc
  apply MeasureTheory.integral_congr_ae
  filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin n))).ae_ne
    (0 : EuclideanSpace ℝ (Fin n))] with x hx
  rw [apm_m95J02_laplacian_regularizedFundamental_of_two_lt hn
    (inv_ne_zero (ne_of_gt hc)) hx]
  rw [← apm_m95J02_peakProfile_scale_of_two_lt hn hc x]
  simp

lemma apm_m95J02_abs_log_sq_add_sq_le
    {r ε : ℝ} (hr : 0 < r) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    |Real.log (r ^ 2 + ε ^ 2)| ≤
      2 * |Real.log r| + Real.log 2 := by
  have harg : 0 < r ^ 2 + ε ^ 2 := by positivity
  have hεsq : ε ^ 2 ≤ 1 := by nlinarith
  by_cases hr1 : r ≤ 1
  · have hrsq : r ^ 2 ≤ 1 := by nlinarith
    have hu : Real.log (r ^ 2 + ε ^ 2) ≤ Real.log 2 :=
      Real.log_le_log harg (by nlinarith)
    have hl : 2 * Real.log r ≤ Real.log (r ^ 2 + ε ^ 2) := by
      have hl' : Real.log (r ^ 2) ≤ Real.log (r ^ 2 + ε ^ 2) :=
        Real.log_le_log (by positivity) (by nlinarith [sq_nonneg ε])
      rw [Real.log_pow] at hl'
      norm_num at hl' ⊢
      exact hl'
    rw [abs_le]
    constructor
    · have ha := neg_abs_le (Real.log r)
      have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      linarith
    · have ha := abs_nonneg (Real.log r)
      linarith
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1'
    have harg1 : 1 ≤ r ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg ε]
    rw [abs_of_nonneg (Real.log_nonneg harg1), abs_of_nonneg hlogr]
    have hu : Real.log (r ^ 2 + ε ^ 2) ≤ Real.log (2 * r ^ 2) :=
      Real.log_le_log harg (by nlinarith)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hu
    convert hu using 1 <;> ring

noncomputable def apm_m95J02_logPairingBound
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  |apm_m95J02_fundamental 2 x * g x| +
    (Real.log 2 / (4 * Real.pi)) * |g x|

lemma apm_m95J02_logPairingBound_integrable
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (apm_m95J02_logPairingBound g) volume := by
  apply Integrable.add
  · have hloc := apm_m95J02_fundamental_locallyIntegrable
      (n := 2) (by omega : 2 ≤ 2)
    have hi : Integrable (fun x => apm_m95J02_fundamental 2 x * g x) volume := by
      simpa [smul_eq_mul] using
        hloc.integrable_smul_right_of_hasCompactSupport hg hgc
    exact hi.norm
  · exact (hg.integrable_of_hasCompactSupport hgc).norm.const_mul _

lemma apm_m95J02_regularizedFundamental_two_mul_norm_le_bound
    {c : ℝ} (hc : 1 ≤ c) {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0)
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) :
    ‖apm_m95J02_regularizedFundamental 2 c⁻¹ x * g x‖ ≤
      apm_m95J02_logPairingBound g x := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hε0 : 0 ≤ c⁻¹ := (inv_pos.mpr hc0).le
  have hε1 : c⁻¹ ≤ 1 := (inv_le_one₀ hc0).mpr hc
  have hlog := apm_m95J02_abs_log_sq_add_sq_le hr hε0 hε1
  rw [Real.norm_eq_abs, abs_mul]
  unfold apm_m95J02_regularizedFundamental apm_m95J02_logPairingBound
  unfold apm_m95J02_fundamental
  simp only [ite_true]
  simp only [abs_div, abs_mul]
  norm_num [abs_of_pos Real.pi_pos]
  have hlog' : |Real.log (‖x‖ ^ 2 + (c ^ 2)⁻¹)| ≤
      2 * |Real.log ‖x‖| + Real.log 2 := by
    simpa [inv_pow] using hlog
  have hg0 : 0 ≤ |g x| := abs_nonneg _
  calc
    |Real.log (‖x‖ ^ 2 + (c ^ 2)⁻¹)| / (4 * Real.pi) * |g x| ≤
        (2 * |Real.log ‖x‖| + Real.log 2) / (4 * Real.pi) * |g x| := by
      gcongr
    _ = |Real.log ‖x‖| / (2 * Real.pi) * |g x| +
        Real.log 2 / (4 * Real.pi) * |g x| := by
      field_simp
      ring

lemma apm_m95J02_regularized_pairing_tendsto_two
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        apm_m95J02_regularizedFundamental 2 c⁻¹ x * g x)
      Filter.atTop
      (nhds (∫ x, apm_m95J02_fundamental 2 x * g x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (apm_m95J02_logPairingBound g)
  · filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with c hc
    exact ((apm_m95J02_regularizedFundamental_contDiff 2
      (inv_ne_zero hc)).continuous.mul hg).aestronglyMeasurable
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with c hc
    have hne : ∀ᵐ x : EuclideanSpace ℝ (Fin 2) ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx
    exact apm_m95J02_regularizedFundamental_two_mul_norm_le_bound hc hx g
  · exact apm_m95J02_logPairingBound_integrable g hg hgc
  · have hne : ∀ᵐ x : EuclideanSpace ℝ (Fin 2) ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx
    have hk := (apm_m95J02_regularizedFundamental_tendsto (n := 2) hx).comp
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun c : ℝ => c⁻¹)
        Filter.atTop (nhds 0))
    exact hk.mul_const (g x)

lemma apm_m95J02_laplacian_continuous_of_smooth
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    Continuous (Laplacian.laplacian φ) := by
  let ψ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℝ :=
    hφc.toSchwartzMap (hφ.of_le (by norm_cast))
  convert (Laplacian.laplacian ψ).continuous using 1
  funext x
  rw [SchwartzMap.laplacian_apply]
  rfl

lemma apm_m95J02_laplacian_hasCompactSupport
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφc : HasCompactSupport φ) :
    HasCompactSupport (Laplacian.laplacian φ) := by
  apply (hφc.iteratedFDeriv (𝕜 := ℝ) 2).mono
  intro x hx hzero
  apply hx
  calc
    Laplacian.laplacian φ x =
        ∑ i : Fin n, iteratedFDeriv ℝ 2 φ x
          ![(EuclideanSpace.basisFun (Fin n) ℝ) i,
            (EuclideanSpace.basisFun (Fin n) ℝ) i] :=
      congrFun
        (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
          (EuclideanSpace.basisFun (Fin n) ℝ)) x
    _ = 0 := by rw [hzero]; simp

lemma apm_m95J02_regularized_pairing_tendsto_of_two_lt
    {n : ℕ} (hn : 2 < n) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Filter.Tendsto
      (fun c : ℝ => ∫ x,
        apm_m95J02_regularizedFundamental n c⁻¹ x * g x)
      Filter.atTop
      (nhds (∫ x, apm_m95J02_fundamental n x * g x)) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let bound : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => |apm_m95J02_fundamental n x * g x|
  apply tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with c hc
    exact ((apm_m95J02_regularizedFundamental_contDiff n (inv_ne_zero hc)).continuous.mul
      hg).aestronglyMeasurable
  · filter_upwards [] with c
    have hne : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    dsimp [bound]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (apm_m95J02_regularizedFundamental_abs_le_of_two_lt hn hx)
      (abs_nonneg _)
  · have hi : Integrable
        (fun x => apm_m95J02_fundamental n x * g x) volume := by
      have hloc := apm_m95J02_fundamental_locallyIntegrable
        (n := n) (by omega : 2 ≤ n)
      simpa [smul_eq_mul] using
        hloc.integrable_smul_right_of_hasCompactSupport hg hgc
    exact hi.norm
  · have hne : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx
    have hk := (apm_m95J02_regularizedFundamental_tendsto (n := n) hx).comp
      (tendsto_inv_atTop_zero : Filter.Tendsto (fun c : ℝ => c⁻¹)
        Filter.atTop (nhds 0))
    exact hk.mul_const (g x)

theorem apm_m95j02
    (n : ℕ) (hn : 2 ≤ n) :
    (∀ (v : ℝ → ℝ) (x : EuclideanSpace ℝ (Fin n)),
      ContDiff ℝ 2 v → x ≠ 0 →
        Laplacian.laplacian (fun z : EuclideanSpace ℝ (Fin n) ↦ v ‖z‖) x =
          iteratedDeriv 2 v ‖x‖ +
            ((n : ℝ) - 1) / ‖x‖ * deriv v ‖x‖) ∧
    (∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∫ x, apm_m95J02_fundamental n x * Laplacian.laplacian φ x) = φ 0) ∧
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f →
        ∀ x : EuclideanSpace ℝ (Fin n),
          Laplacian.laplacian (apm_m95J02_poissonSolution n f) x = f x) := by
  /-
  Boundary (closer hop 1): the dimensional normalization is now compiled.
  `apm_m95J02_sphereArea_two` proves that the Gamma-function definition gives
  `ω₂ = 2π`, and `apm_m95J02_fundamental_two` exposes the exact logarithmic
  branch used in the weak identity.  This also sanity-checks the sign: the
  file uses `+ log ‖x‖ / (2π)` in dimension two and
  `-‖x‖^(2-n) / ((n-2)ωₙ)` otherwise, both corresponding to `ΔΦ = δ`.

  Closer hop 2 extends that normalization beyond the special dimension.
  `apm_m95J02_sphereArea_pos` proves positivity of the Gamma-defined sphere
  area in every positive dimension. `apm_m95J02_power_denominator_pos` proves
  the complete power-branch denominator positive for `n > 2`, and
  `apm_m95J02_fundamental_neg` uses it to certify the expected strict negative
  sign of the kernel away from its pole. Thus all dimension-dependent sign and
  denominator obligations are now compiled.

  Closer hop 3 goes beyond normalization by separating the actual scalar
  calculus from the Euclidean chain rule. `apm_m95J02_radialProfile` factors
  the kernel through the radius,
  `apm_m95J02_fundamental_eq_radialProfile` records that factorization, and
  `apm_m95J02_hasDerivAt_radialProfile_of_two_lt` proves the power-law
  profile's derivative at every nonzero radius directly from Mathlib's real
  `rpow` derivative theorem. This is a compiled analytic input to part (a),
  not merely another sign check.

  Searches across both hops of `LEMMA-INDEX.md`, `ConstructionTargets`, Mathlib's new
  `Analysis.InnerProductSpace.Laplacian`, Schwartz-space integration by parts,
  prior radial-integration artifacts (`a95A03`, `m94A03`, and `m96J03`), and
  git history found no radial-composition Laplacian formula or singular-kernel
  convolution theorem.  Mathlib exposes the Laplacian through second Fréchet
  derivatives and orthonormal bases, but the chain rule for `z ↦ v ‖z‖`, the
  punctured-ball boundary limit, and differentiation of the singular
  convolution remain to be developed locally.

  The final-hop search additionally checked the full repository lemma index,
  `ConstructionTargets`, the concrete planar fundamental-solution artifact
  `m02A03`, Mathlib's Laplacian, Schwartz/tempered-distribution, convolution,
  and real-power derivative sources, and this bundle's git history. The
  real-power API supplied the new scalar derivative lemma; the other sources
  still contain no radial norm-composition Laplacian theorem, punctured-ball
  Green identity, or singular-convolution differentiation theorem. The
  theorem-level bridge therefore remains open and the frozen statement is
  unchanged.

  Original boundary:
  SKIPPED: fundamental solution of Laplacian (three-part PDE problem).
  -- (a) Laplacian of radial function: Δv(|x|) = v''(r) + (n-1)/r · v'(r).
  -- (b) ΔΦ = δ in distributions: ∫ Φ·Δφ = φ(0) for test functions φ.
  -- (c) Poisson solution: Δ(Φ*f) = f for compactly supported smooth f.
  -- Blocker: requires Laplacian on Euclidean space, distributional PDE theory,
  -- Green's function computation, convolution with singular kernels — none of
  -- which have ready-to-use Mathlib infrastructure.
  APIs: `Laplacian.laplacian`, `ContDiff`, `HasCompactSupport`, `EuclideanSpace`.
  -/
  have hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
        (∫ x, apm_m95J02_fundamental n x * Laplacian.laplacian φ x) = φ 0 := by
    let c : ℕ → ℝ := fun k => (k : ℝ) + 1
    let K : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
      apm_m95J02_regularizedFundamental n (c k)⁻¹
    let ρ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
      Laplacian.laplacian (K k)
    apply apm_m95J02_weakIdentity_of_regularization_family K ρ
    · intro φ hφ hφc
      have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ :=
        hφ.of_le (by norm_cast)
      have hlcont := apm_m95J02_laplacian_continuous_of_smooth φ hφ' hφc
      have hlcomp := apm_m95J02_laplacian_hasCompactSupport φ hφc
      have hc : Filter.Tendsto c Filter.atTop Filter.atTop := by
        dsimp [c]
        exact Filter.tendsto_atTop_add_const_right Filter.atTop 1
          (tendsto_natCast_atTop_atTop (R := ℝ))
      by_cases hn2 : n = 2
      · subst n
        simpa [K, c] using
          (apm_m95J02_regularized_pairing_tendsto_two
            (Laplacian.laplacian φ) hlcont hlcomp).comp hc
      · have hnlt : 2 < n := by omega
        simpa [K, c] using
          (apm_m95J02_regularized_pairing_tendsto_of_two_lt hnlt
            (Laplacian.laplacian φ) hlcont hlcomp).comp hc
    · intro φ hφ hφc k
      have hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ :=
        hφ.of_le (by norm_cast)
      exact apm_m95J02_regularizedFundamental_green_identity
        (inv_ne_zero (by dsimp [c]; positivity)) φ hφ' hφc
    · intro φ hφ hφc
      have hc : Filter.Tendsto c Filter.atTop Filter.atTop := by
        dsimp [c]
        exact Filter.tendsto_atTop_add_const_right Filter.atTop 1
          (tendsto_natCast_atTop_atTop (R := ℝ))
      by_cases hn2 : n = 2
      · subst n
        simpa [ρ, K, c] using
          (apm_m95J02_regularized_density_tendsto_two φ hφ.continuous hφc).comp hc
      · have hnlt : 2 < n := by omega
        simpa [ρ, K, c] using
          (apm_m95J02_regularized_density_tendsto_of_two_lt hnlt
            φ hφ.continuous hφc).comp hc
  refine ⟨?_, hweak, ?_⟩
  · intro v x hv hx
    exact apm_m95J02_laplacian_radial v x hv.contDiffAt hx
  · intro f hf hfc x
    exact apm_m95J02_poisson_eq_of_weakIdentity hn hweak f hf hfc x
