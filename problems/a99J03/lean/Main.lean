import Mathlib

/-!
# APM a99J03: A Stieltjes transform of an `L¹` function

## Statement repairs

None.

## Encoding questions

None. The source's `L¹((0,∞))` is interpreted for real-valued functions
using Lebesgue measure. The final question at `a = 0` is encoded by the
explicit counterexample `1_(0,1)`.
-/

open MeasureTheory Set Filter
open scoped ContDiff

noncomputable section

/-- The Stieltjes-type transform in the problem. -/
def apm_a99J03_transform (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), f y / (x + y)

/-- The counterexample `f = 1_(0,1)` for the endpoint question. -/
def apm_a99J03_counterexample (y : ℝ) : ℝ :=
  (Ioo (0 : ℝ) 1).indicator (fun _ ↦ 1) y

/-- The endpoint counterexample is an `L¹` function; its support is the bounded
interval `(0,1)`. -/
lemma apm_a99J03_counterexample_integrableOn :
    IntegrableOn apm_a99J03_counterexample (Ioi 0) := by
  have hconst : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioo 0 1) :=
    integrableOn_const (by simp [Real.volume_Ioo])
  have hind : Integrable ((Ioo (0 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ))) :=
    hconst.integrable_indicator measurableSet_Ioo
  exact hind.integrableOn

/-- Pointwise parameter derivative of the Stieltjes kernel.  This is the
calculus input to Mathlib's dominated parametric-integral theorem. -/
lemma apm_a99J03_hasDerivAt_kernel
    (f : ℝ → ℝ) {x y : ℝ} (hxy : x + y ≠ 0) :
    HasDerivAt (fun z : ℝ ↦ f y / (z + y)) (-f y / (x + y) ^ 2) x := by
  have hden : HasDerivAt (fun z : ℝ ↦ z + y) 1 x :=
    (hasDerivAt_id x).add_const y
  convert (hasDerivAt_const x (f y)).div hden hxy using 1 <;> ring

/-- Uniform domination of the kernel derivative on the neighborhood
`(x/2, 3x/2)` used for differentiation under the integral sign. -/
lemma apm_a99J03_kernel_deriv_bound
    (f : ℝ → ℝ) {x z y : ℝ} (hx : 0 < x)
    (hz : z ∈ Ioo (x / 2) (3 * x / 2)) (hy : 0 < y) :
    |(-f y) / (z + y) ^ 2| ≤ |f y| / (x / 2) ^ 2 := by
  have hx2 : 0 < x / 2 := by positivity
  have hzy : x / 2 < z + y := by linarith [hz.1]
  have hzy0 : 0 < z + y := hx2.trans hzy
  have habszy : |z + y| = z + y := abs_of_pos hzy0
  rw [abs_div, abs_neg, abs_pow, habszy]
  exact div_le_div_of_nonneg_left (abs_nonneg (f y)) (sq_pos_of_pos hx2)
    ((sq_le_sq₀ hx2.le hzy0.le).2 hzy.le)

/-- Differentiation under the integral sign at a positive parameter. -/
lemma apm_a99J03_hasDerivAt_transform
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (apm_a99J03_transform f)
      (-(∫ y in Ioi (0 : ℝ), f y / (x + y) ^ 2)) x := by
  let s : Set ℝ := Ioo (x / 2) (3 * x / 2)
  let F : ℝ → ℝ → ℝ := fun z y ↦ f y / (z + y)
  let F' : ℝ → ℝ → ℝ := fun z y ↦ -f y / (z + y) ^ 2
  let bound : ℝ → ℝ := fun y ↦ |f y| / (x / 2) ^ 2
  have hs : s ∈ nhds x := by
    apply Ioo_mem_nhds
    · linarith
    · linarith
  have hF_meas : ∀ᶠ z in nhds x, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    filter_upwards [hs] with z hz
    dsimp [F]
    exact hf.aestronglyMeasurable.mul
      (measurable_inv.aestronglyMeasurable.comp_measurable (measurable_const.add measurable_id))
  have hF_int : Integrable (F x) (volume.restrict (Ioi 0)) := by
    apply (hf.norm.const_mul x⁻¹).mono'
    · exact hF_meas.self_of_nhds
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      change 0 < y at hy
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < x + y)]
      change |f y| / (x + y) ≤ x⁻¹ * |f y|
      calc
        |f y| / (x + y) ≤ |f y| / x :=
          div_le_div_of_nonneg_left (abs_nonneg (f y)) hx (by linarith)
        _ = x⁻¹ * |f y| := by field_simp
  have hF'_meas : AEStronglyMeasurable (F' x) (volume.restrict (Ioi 0)) := by
    dsimp [F']
    exact hf.aestronglyMeasurable.neg.mul
      (measurable_inv.aestronglyMeasurable.comp_measurable
        ((measurable_const.add measurable_id).pow_const 2))
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    simpa [bound, div_eq_mul_inv, mul_comm] using
      hf.norm.const_mul (((x / 2) ^ 2)⁻¹)
  have h_bound : ∀ᵐ y ∂(volume.restrict (Ioi 0)), ∀ z ∈ s, ‖F' z y‖ ≤ bound y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    simpa [F', bound, Real.norm_eq_abs, div_eq_mul_inv] using
      apm_a99J03_kernel_deriv_bound f hx hz hy
  have h_diff : ∀ᵐ y ∂(volume.restrict (Ioi 0)), ∀ z ∈ s,
      HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    change 0 < y at hy
    exact apm_a99J03_hasDerivAt_kernel f (by
      have : x / 2 < z := hz.1
      linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int
    hF'_meas h_bound hbound h_diff
  convert h.2 using 1
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp [F']
  ring

/-- Higher-order Stieltjes kernels used to iterate differentiation. -/
def apm_a99J03_transformPow (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), f y / (x + y) ^ (n + 1)

lemma apm_a99J03_hasDerivAt_kernelPow
    (f : ℝ → ℝ) (n : ℕ) {x y : ℝ} (hxy : x + y ≠ 0) :
    HasDerivAt (fun z : ℝ ↦ f y / (z + y) ^ (n + 1))
      (-((n + 1 : ℕ) : ℝ) * f y / (x + y) ^ (n + 2)) x := by
  have hden : HasDerivAt (fun z : ℝ ↦ z + y) 1 x :=
    (hasDerivAt_id x).add_const y
  convert (hasDerivAt_const x (f y)).div (hden.pow (n + 1))
    (pow_ne_zero _ hxy) using 1 <;> field_simp [hxy] <;> simp [pow_succ] <;> ring

lemma apm_a99J03_kernelPow_deriv_bound
    (f : ℝ → ℝ) (n : ℕ) {x z y : ℝ} (hx : 0 < x)
    (hz : z ∈ Ioo (x / 2) (3 * x / 2)) (hy : 0 < y) :
    ‖-((n + 1 : ℕ) : ℝ) * f y / (z + y) ^ (n + 2)‖ ≤
      ((n + 1 : ℕ) : ℝ) * |f y| / (x / 2) ^ (n + 2) := by
  have hx2 : 0 < x / 2 := by positivity
  have hzy : x / 2 < z + y := by linarith [hz.1]
  have habszy : |z + y| = z + y := abs_of_pos (hx2.trans hzy)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg _), abs_pow, habszy]
  exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg (f y)))
    (pow_pos hx2 _) (pow_le_pow_left₀ hx2.le hzy.le (n + 2))

lemma apm_a99J03_hasDerivAt_transformPow
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (apm_a99J03_transformPow f n)
      (-((n + 1 : ℕ) : ℝ) * apm_a99J03_transformPow f (n + 1) x) x := by
  let s : Set ℝ := Ioo (x / 2) (3 * x / 2)
  let F : ℝ → ℝ → ℝ := fun z y ↦ f y / (z + y) ^ (n + 1)
  let F' : ℝ → ℝ → ℝ :=
    fun z y ↦ -((n + 1 : ℕ) : ℝ) * f y / (z + y) ^ (n + 2)
  let bound : ℝ → ℝ :=
    fun y ↦ ((n + 1 : ℕ) : ℝ) * |f y| / (x / 2) ^ (n + 2)
  have hs : s ∈ nhds x := by
    apply Ioo_mem_nhds <;> linarith
  have hF_meas : ∀ᶠ z in nhds x,
      AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := by
    filter_upwards [hs] with z hz
    dsimp [F]
    exact hf.aestronglyMeasurable.mul
      (measurable_inv.aestronglyMeasurable.comp_measurable
        ((measurable_const.add measurable_id).pow_const (n + 1)))
  have hF_int : Integrable (F x) (volume.restrict (Ioi 0)) := by
    apply (hf.norm.const_mul ((x ^ (n + 1))⁻¹)).mono'
    · exact hF_meas.self_of_nhds
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      change 0 < y at hy
      rw [Real.norm_eq_abs, abs_div, abs_pow,
        abs_of_pos (by linarith : 0 < x + y)]
      change |f y| / (x + y) ^ (n + 1) ≤ (x ^ (n + 1))⁻¹ * |f y|
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (abs_nonneg (f y)) (pow_pos hx _)
        (pow_le_pow_left₀ hx.le (by linarith : x ≤ x + y) (n + 1))
  have hF'_meas : AEStronglyMeasurable (F' x) (volume.restrict (Ioi 0)) := by
    dsimp [F']
    have hm := (hf.aestronglyMeasurable.const_mul (-((n + 1 : ℕ) : ℝ))).mul
        (measurable_inv.aestronglyMeasurable.comp_measurable
          (((measurable_const : Measurable (fun _ : ℝ ↦ x)).add measurable_id).pow_const
            (n + 2)))
    convert hm using 1
  have hbound : Integrable bound (volume.restrict (Ioi 0)) := by
    simpa [bound, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hf.norm.const_mul
        ((((n + 1 : ℕ) : ℝ) / (x / 2) ^ (n + 2)))
  have h_bound : ∀ᵐ y ∂(volume.restrict (Ioi 0)), ∀ z ∈ s, ‖F' z y‖ ≤ bound y := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    exact apm_a99J03_kernelPow_deriv_bound f n hx hz hy
  have h_diff : ∀ᵐ y ∂(volume.restrict (Ioi 0)), ∀ z ∈ s,
      HasDerivAt (F · y) (F' z y) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy z hz
    change 0 < y at hy
    exact apm_a99J03_hasDerivAt_kernelPow f n (by
      have : x / 2 < z := hz.1
      linarith)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int
    hF'_meas h_bound hbound h_diff
  convert h.2 using 1
  simp only [apm_a99J03_transformPow, F', Nat.add_assoc]
  rw [show n + (1 + 1) = n + 2 by omega]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

lemma apm_a99J03_transformPow_contDiffOn
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) (m n : ℕ) :
    ContDiffOn ℝ m (apm_a99J03_transformPow f n) (Ioi 0) := by
  induction m generalizing n with
  | zero =>
      norm_num only [Nat.cast_zero]
      rw [contDiffOn_zero]
      intro x hx
      exact (apm_a99J03_hasDerivAt_transformPow f hf n hx).differentiableAt.continuousAt.continuousWithinAt
  | succ m ih =>
      norm_num only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨fun x hx ↦
          (apm_a99J03_hasDerivAt_transformPow f hf n hx).differentiableAt.differentiableWithinAt,
        ?_, ?_⟩
      · intro htop
        norm_num at htop
      · have hc : ContDiffOn ℝ m
            (fun x ↦ -((n + 1 : ℕ) : ℝ) * apm_a99J03_transformPow f (n + 1) x)
            (Ioi 0) := by
              simpa only [smul_eq_mul] using
                ContDiffOn.const_smul (-((n + 1 : ℕ) : ℝ)) (ih (n + 1))
        apply hc.congr
        intro x hx
        exact (apm_a99J03_hasDerivAt_transformPow f hf n hx).deriv

/-- The elementary endpoint kernel arising from the indicator datum is not
integrable near zero. -/
lemma apm_a99J03_endpoint_kernel_not_integrable :
    ¬ IntegrableOn (fun x : ℝ => 1 / (x * (x + 1))) (Ioo 0 1) volume := by
  intro hker
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioo 0 1) volume := by
    apply (hker.const_mul 2).mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hx0 : 0 < x := hx.1
    have hx1 : x + 1 ≤ 2 := by linarith [hx.2]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
    have hden : 0 < x * (x + 1) := mul_pos hx0 (by linarith)
    calc
      x⁻¹ = (x + 1) / (x * (x + 1)) := by field_simp
      _ ≤ 2 / (x * (x + 1)) := (div_le_div_iff_of_pos_right hden).2 hx1
      _ = 2 * (1 / (x * (x + 1))) := by rw [div_eq_mul_inv, one_div]
  have hrpow : IntegrableOn (fun x : ℝ => x ^ (-1 : ℝ)) (Ioo 0 1) volume := by
    refine hinv.congr_fun ?_ measurableSet_Ioo
    intro x hx
    simpa only using (Real.rpow_neg_one x).symm
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one] at hrpow
  norm_num at hrpow

/-- Exact integral of the squared Stieltjes kernel over the counterexample's
support. -/
lemma apm_a99J03_integral_sq_kernel (x : ℝ) (hx : 0 < x) :
    ∫ y in Ioo (0 : ℝ) 1, 1 / (x + y) ^ 2 = 1 / (x * (x + 1)) := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  let g : ℝ → ℝ := fun y ↦ -(x + y)⁻¹
  have hderiv : deriv g = fun y ↦ 1 / (x + y) ^ 2 := by
    funext y
    calc
      deriv g y = -deriv (fun y : ℝ ↦ (x + y)⁻¹) y := by
        exact deriv.neg
      _ = -deriv (fun t : ℝ ↦ t⁻¹) (x + y) := by
        rw [deriv_comp_const_add]
      _ = 1 / (x + y) ^ 2 := by rw [deriv_inv]; ring
  rw [← hderiv, intervalIntegral.integral_deriv_eq_sub]
  · dsimp [g]
    field_simp
    <;> ring
  · intro y hy
    apply DifferentiableAt.neg
    apply DifferentiableAt.inv
    · fun_prop
    · have hy0 : 0 ≤ y := by simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hy.1
      linarith
  · apply ContinuousOn.intervalIntegrable
    rw [hderiv]
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_const.add continuousOn_id).pow 2)
    intro y hy
    have hy0 : 0 ≤ y := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hy.1
    change (x + y) ^ 2 ≠ 0
    exact pow_ne_zero 2 (by linarith)

/-- Why this unblocks `apm_a99j03`: this is the dominated-differentiation
package, including its iteration, for the Stieltjes kernel.  Its first
component is the first conjunct of the main theorem, while its second
component supplies the derivative formula used by both integrability
arguments. -/
theorem apm_a99J03_bridge_smooth_and_deriv
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
    ContDiffOn ℝ ∞ (apm_a99J03_transform f) (Ioi 0) ∧
      ∀ x : ℝ, 0 < x →
        deriv (apm_a99J03_transform f) x =
          -(∫ y in Ioi (0 : ℝ), f y / (x + y) ^ 2) := by
  constructor
  · rw [contDiffOn_infty]
    intro m
    have heq : apm_a99J03_transform f = apm_a99J03_transformPow f 0 := by
      funext x
      simp [apm_a99J03_transform, apm_a99J03_transformPow]
    rw [heq]
    exact apm_a99J03_transformPow_contDiffOn f hf m 0
  · intro x hx
    exact (apm_a99J03_hasDerivAt_transform f hf hx).deriv

/-- Why this unblocks `apm_a99j03`: this is exactly the Tonelli estimate
away from the singular endpoint.  It supplies the second conjunct after the
derivative has been identified by the preceding bridge. -/
theorem apm_a99J03_bridge_deriv_integrableOn_Ici
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0))
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn (deriv (apm_a99J03_transform f)) (Ici a) := by
  let μx := volume.restrict (Ici a)
  let μy := volume.restrict (Ioi (0 : ℝ))
  let K : ℝ × ℝ → ℝ := fun p ↦ -f p.2 / (p.1 + p.2) ^ 2
  have hrpow : Integrable (fun x : ℝ ↦ x ^ (-2 : ℝ)) μx := by
    dsimp [μx]
    apply (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun x : ℝ ↦ x ^ (-2 : ℝ))).mpr
    exact integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  have hmajor : Integrable (fun p : ℝ × ℝ ↦ p.1 ^ (-2 : ℝ) * |f p.2|)
      (μx.prod μy) := hrpow.mul_prod hf.norm
  have hK : Integrable K (μx.prod μy) := by
    apply hmajor.mono'
    · dsimp [K]
      exact (hf.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_snd).neg.mul
          (measurable_inv.aestronglyMeasurable.comp_measurable
            ((measurable_fst.add measurable_snd).pow_const 2))
    · simp only [μx, μy, Measure.prod_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ici.prod measurableSet_Ioi)] with p hp
      have hpa : a ≤ p.1 := hp.1
      have hp2 : 0 < p.2 := hp.2
      have hp1 : 0 < p.1 := ha.trans_le hpa
      rw [Real.norm_eq_abs, abs_div, abs_neg, abs_pow,
        abs_of_pos (by linarith : 0 < p.1 + p.2)]
      change |f p.2| / (p.1 + p.2) ^ 2 ≤ p.1 ^ (-2 : ℝ) * |f p.2|
      rw [Real.rpow_neg (le_of_lt hp1)]
      rw [Real.rpow_two]
      rw [inv_mul_eq_div]
      exact div_le_div_of_nonneg_left (abs_nonneg (f p.2)) (sq_pos_of_pos hp1)
        ((sq_le_sq₀ hp1.le (by linarith : 0 ≤ p.1 + p.2)).2 (by linarith))
  have hinter : Integrable (fun x ↦ ∫ y, K (x, y) ∂μy) μx := hK.integral_prod_left
  apply hinter.congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have hx0 : 0 < x := ha.trans_le hx
  rw [(apm_a99J03_hasDerivAt_transform f hf hx0).deriv]
  dsimp [K, μy]
  calc
    (∫ y in Ioi (0 : ℝ), -f y / (x + y) ^ 2) =
        ∫ y in Ioi (0 : ℝ), -(f y / (x + y) ^ 2) := by
          apply integral_congr_ae
          filter_upwards [] with y
          ring
    _ = -(∫ y in Ioi (0 : ℝ), f y / (x + y) ^ 2) := integral_neg _

/-- Why this unblocks `apm_a99j03`: it specializes dominated differentiation
to the indicator datum and identifies the derivative norm with the elementary
kernel already proved nonintegrable above.  Restriction from `(0,∞)` to
`(0,1)` then gives the final contradiction. -/
theorem apm_a99J03_bridge_counterexample_deriv_norm
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ‖deriv (apm_a99J03_transform apm_a99J03_counterexample) x‖ =
      1 / (x * (x + 1)) := by
  rw [(apm_a99J03_hasDerivAt_transform apm_a99J03_counterexample
    apm_a99J03_counterexample_integrableOn hx.1).deriv, norm_neg, Real.norm_eq_abs]
  have hint :
      (∫ y in Ioi (0 : ℝ), apm_a99J03_counterexample y / (x + y) ^ 2) =
        1 / (x * (x + 1)) := by
    rw [show (fun y : ℝ ↦ apm_a99J03_counterexample y / (x + y) ^ 2) =
        (Ioo (0 : ℝ) 1).indicator (fun y ↦ 1 / (x + y) ^ 2) by
      funext y
      simp only [apm_a99J03_counterexample]
      by_cases hy : y ∈ Ioo (0 : ℝ) 1 <;> simp [hy]]
    rw [setIntegral_indicator measurableSet_Ioo]
    simpa only [inter_eq_right.mpr Ioo_subset_Ioi_self] using
      apm_a99J03_integral_sq_kernel x hx.1
  rw [hint, abs_of_pos]
  exact div_pos zero_lt_one (mul_pos hx.1 (add_pos hx.1 zero_lt_one))

theorem apm_a99j03
    (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) :
    ContDiffOn ℝ ∞ (apm_a99J03_transform f) (Ioi 0) ∧
    (∀ a : ℝ, 0 < a →
      IntegrableOn (deriv (apm_a99J03_transform f)) (Ici a)) ∧
    IntegrableOn apm_a99J03_counterexample (Ioi 0) ∧
    ¬IntegrableOn
      (deriv (apm_a99J03_transform apm_a99J03_counterexample))
      (Ioi 0) := by
  rcases apm_a99J03_bridge_smooth_and_deriv f hf with ⟨hsmooth, _⟩
  refine ⟨hsmooth, fun a ha ↦ apm_a99J03_bridge_deriv_integrableOn_Ici f hf ha,
    apm_a99J03_counterexample_integrableOn, ?_⟩
  intro hendpoint
  apply apm_a99J03_endpoint_kernel_not_integrable
  have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi 0 := fun _ hz ↦ hz.1
  have hnorm := (hendpoint.mono_set hsub).norm
  apply hnorm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact apm_a99J03_bridge_counterexample_deriv_norm hx
  /-
  Boundary (closer hop 3): `apm_a99J03_counterexample_integrableOn` above
  closes the third conjunct directly from bounded support.  Searches of
  `LEMMA-INDEX.md`, all `ConstructionTargets/`, closed siblings, and Mathlib's
  parameter-integral APIs found the reusable theorem
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`; siblings `a01A09`,
  `a01A11`, and `a96A04` demonstrate its use.  No packaged Stieltjes-transform
  smoothness theorem was found.

  Closer hop 2 proves the two central pointwise inputs to that theorem:
  `apm_a99J03_hasDerivAt_kernel` gives the exact parameter derivative, and
  `apm_a99J03_kernel_deriv_bound` proves its uniform domination on the
  neighborhood `(x/2, 3*x/2)` by `|f y|/(x/2)^2`.

  The remaining common bridge is to package these facts into, for `x > 0`,

  `deriv (apm_a99J03_transform f) x =
     -∫ y in Ioi 0, f y / (x+y)^2`.

  including all measurability and restricted-integrability obligations.
  Iterating the same argument gives `ContDiffOn`; Tonelli then yields
  the derivative `L¹(Ici a)` estimate.  For the counterexample the displayed
  formula reduces to `-1/x + 1/(x+1)`, whose absolute value is
  `1/(x*(x+1))`; the final blocker is its nonintegrability at zero via the
  power-integrability API.  Thus the explicit datum's integrability is proved,
  while differentiation under the improper integral remains open.

  Closer hop 3 proves `apm_a99J03_endpoint_kernel_not_integrable`. It compares
  `x⁻¹` with twice `1/(x*(x+1))` on `(0,1)` and invokes Mathlib's exact
  `integrableOn_Ioo_rpow_iff` criterion at exponent `-1`. Thus, once the
  counterexample derivative is rewritten to the displayed elementary kernel,
  its endpoint failure is completely discharged. Renewed inspection of the
  parametric-integral examples in `a01A09`, `a01A11`, and `a96A04` did not
  yield a packaged iteration from the first derivative formula to the frozen
  `ContDiffOn ∞` statement. The remaining bridge is precisely that dominated
  differentiation packaging, its iteration, and the Tonelli estimate away
  from zero.
  -/
