/-
! # APM a96A04: heat kernel on ℝⁿ — smoothness, L² contraction, L² limit

The printed `L²(ℝ)` is a typo for `L²(ℝⁿ)` (see PRELIM-DEFECT.md); the problem is the
standard n-dimensional statement: for `f ∈ L²(ℝⁿ)` (complex-valued, Lebesgue
measurable) and `t > 0`, with

  `u(x,t) = (4πt)^(-n/2) ∫ exp(-‖x-y‖²/(4t)) • f(y) dy`,

(a) `u(·,t)` is smooth on `ℝⁿ`;
(b) `‖u(·,t)‖₂ ≤ ‖f‖₂`;
(c) `u(·,t) → f` in `L²` as `t → 0⁺`.

Everything is done on `EuclideanSpace ℝ (Fin n)` with its Lebesgue (`volume`)
measure, which is an additive Haar measure.
-/

import Mathlib

open MeasureTheory Set Filter Real Topology

open scoped ENNReal ContDiff BigOperators

noncomputable section

/-! ## Product integrals on `EuclideanSpace ℝ (Fin n)` -/

section Product

variable {n : ℕ}

/-- A product integrand on `EuclideanSpace ℝ (Fin n)` integrates to a product of
one-dimensional integrals. -/
lemma integral_euclidean_prod_eq_prod (h : Fin n → ℝ → ℝ)
    (hint : ∀ i, Integrable (h i) volume) :
    ∫ x : EuclideanSpace ℝ (Fin n), ∏ i, h i (x i) ∂volume
      = ∏ i, ∫ r : ℝ, h i r ∂volume := by
  have hmp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin n → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp (Fin n)
  rw [← hmp.integral_comp' (fun x : EuclideanSpace ℝ (Fin n) => ∏ i, h i (x i))]
  simp only [WithLp.ofLp_toLp]
  exact integral_fintype_prod_volume_eq_prod h

end Product

/-! ## The heat kernel on `EuclideanSpace ℝ (Fin n)` -/

section Kernel

variable {n : ℕ}

lemma euclidean_norm_sq (x : EuclideanSpace ℝ (Fin n)) : ‖x‖ ^ 2 = ∑ i, (x i) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  congr 2 with i
  simp [sq_abs]

lemma exp_neg_norm_sq_eq_prod {t : ℝ} (x : EuclideanSpace ℝ (Fin n)) :
    Real.exp (-‖x‖ ^ 2 / (4 * t)) = ∏ i, Real.exp (-(x i) ^ 2 / (4 * t)) := by
  rw [euclidean_norm_sq, show (-∑ i, (x i) ^ 2) / (4 * t) = ∑ i, (-(x i) ^ 2) / (4 * t) from by
    rw [← Finset.sum_neg_distrib, Finset.sum_div], Real.exp_sum]

lemma integrable_exp_neg_coord_sq {t : ℝ} (ht : 0 < t) (i : Fin n) :
    Integrable (fun r : ℝ => Real.exp (-(r : ℝ) ^ 2 / (4 * t))) volume := by
  have hb : 0 < 1 / (4 * t) := by positivity
  have h := integrable_exp_neg_mul_sq (b := 1 / (4 * t)) hb
  refine h.congr (Eventually.of_forall fun r => ?_)
  congr 1
  field_simp

lemma integrable_exp_neg_norm_sq {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / (4 * t))) volume := by
  have hpi : Integrable (fun v : Fin n → ℝ =>
      ∏ i, Real.exp (-(v i) ^ 2 / (4 * t))) volume :=
    Integrable.fintype_prod (fun i => integrable_exp_neg_coord_sq ht i)
  refine ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_of_integrable
    hpi).congr ?_
  filter_upwards with x
  simp only [Function.comp_apply]
  rw [exp_neg_norm_sq_eq_prod (t := t) x]

lemma integral_exp_neg_norm_sq {t : ℝ} (ht : 0 < t) :
    ∫ x : EuclideanSpace ℝ (Fin n), Real.exp (-‖x‖ ^ 2 / (4 * t)) ∂volume
      = ((4 * π * t) ^ ((1 : ℝ) / 2)) ^ n := by
  have h1 : (∫ r : ℝ, Real.exp (-(r : ℝ) ^ 2 / (4 * t)) ∂volume)
      = (4 * π * t) ^ ((1 : ℝ) / 2) := by
    have hgauss := integral_gaussian (1 / (4 * t))
    rw [show π / (1 / (4 * t)) = 4 * π * t from by field_simp] at hgauss
    rw [show Real.sqrt (4 * π * t) = (4 * π * t) ^ ((1 : ℝ) / 2) from
      Real.sqrt_eq_rpow (4 * π * t)] at hgauss
    refine hgauss.symm ▸ ?_
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    congr 1
    field_simp
  have hexp : (fun x : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x‖ ^ 2 / (4 * t)))
      = fun x => ∏ i, Real.exp (-(x i) ^ 2 / (4 * t)) :=
    funext fun x => exp_neg_norm_sq_eq_prod x
  rw [hexp, integral_euclidean_prod_eq_prod
    (fun i : Fin n => fun r : ℝ => Real.exp (-(r : ℝ) ^ 2 / (4 * t)))
    (fun i => integrable_exp_neg_coord_sq ht i), Finset.prod_const, Finset.card_univ, Fintype.card_fin, h1]

end Kernel

section HeatKernel

variable {n : ℕ}

/-- The heat kernel `G_t(x) = (4πt)^(-n/2) exp(-‖x‖²/(4t))` on `ℝⁿ`. -/
def heatKernelN (n : ℕ) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (4 * π * t) ^ (-(n : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t))

/-- The heat convolution `u(x,t) = ∫ G_t(x-y) • f(y) dy`, complex-valued. -/
def heatConvN (n : ℕ) (t : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∫ y, heatKernelN n t (x - y) • f y ∂volume

lemma heatKernelN_nonneg {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    0 ≤ heatKernelN n t x := by
  unfold heatKernelN
  positivity

lemma heatKernelN_rpow_key {t : ℝ} (ht : 0 < t) :
    (4 * π * t) ^ (-(n : ℝ) / 2) * ((4 * π * t) ^ ((1 : ℝ) / 2)) ^ n = 1 := by
  have hpos : 0 < 4 * π * t := by positivity
  have h1 : ((4 * π * t) ^ ((1 : ℝ) / 2)) ^ n = (4 * π * t) ^ ((n : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le]
    congr 1
    ring
  rw [h1, ← Real.rpow_add hpos, show (-(n : ℝ) / 2) + (n : ℝ) / 2 = 0 from by ring, Real.rpow_zero]

lemma heatKernelN_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : EuclideanSpace ℝ (Fin n), heatKernelN n t x ∂volume = 1 := by
  have hpos : 0 < 4 * π * t := by positivity
  unfold heatKernelN
  rw [integral_const_mul, integral_exp_neg_norm_sq ht,
    heatKernelN_rpow_key ht]

lemma heatKernelN_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (heatKernelN n t) volume :=
  (integrable_exp_neg_norm_sq ht).const_mul _

lemma heatKernelN_lintegral_eq_one {t : ℝ} (ht : 0 < t) :
    ∫⁻ z, ENNReal.ofReal (heatKernelN n t z) ∂volume = 1 := by
  have h1 : (fun z => ENNReal.ofReal (heatKernelN n t z))
      = fun z => ‖heatKernelN n t z‖ₑ := by
    funext z
    rw [show ENNReal.ofReal (heatKernelN n t z) = ENNReal.ofReal ‖heatKernelN n t z‖ from by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatKernelN_nonneg ht z)]]
    exact ofReal_norm_eq_enorm (heatKernelN n t z)
  rw [h1, ← ofReal_integral_norm_eq_lintegral_enorm (heatKernelN_integrable ht)]
  have hnorm : ∀ᵐ x ∂volume, ‖heatKernelN n t x‖ = heatKernelN n t x :=
    Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatKernelN_nonneg ht x)]
  rw [integral_congr_ae hnorm, heatKernelN_integral ht]
  norm_num

end HeatKernel

/-! ## Young's convolution inequality (L² case) on `EuclideanSpace ℝ (Fin n)` -/

section Young

open MeasureTheory

/-- Weighted Cauchy--Schwarz in the nonnegative extended reals. -/
lemma lintegral_weight_mul_sq_le_eucl
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (w v : α → ℝ≥0∞) (hw : AEMeasurable w μ) (hv : AEMeasurable v μ) :
    (∫⁻ x, w x * v x ∂μ) ^ 2 ≤
      (∫⁻ x, w x ∂μ) * (∫⁻ x, w x * v x ^ 2 ∂μ) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ
    Real.HolderConjugate.two_two
    (f := fun x => (w x) ^ (1 / 2 : ℝ))
    (g := fun x => (w x) ^ (1 / 2 : ℝ) * v x)
    (hw.pow_const _)
    ((hw.pow_const _).mul hv)
  simp only [Pi.mul_apply] at h
  have hhalf : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
  have htwice : (1 / 2 : ℝ) * 2 = 1 := by norm_num
  simp_rw [← mul_assoc,
    ← ENNReal.rpow_add_of_nonneg (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num),
    hhalf, ENNReal.rpow_one] at h
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul, htwice, ENNReal.rpow_one] at h
  have hsquare (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  calc
    (∫⁻ x, w x * v x ∂μ) ^ 2
        ≤ (((∫⁻ x, w x ∂μ) ^ (1 / 2 : ℝ)) *
          ((∫⁻ x, w x * v x ^ 2 ∂μ) ^ (1 / 2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (zero_le _) h 2
    _ = (∫⁻ x, w x ∂μ) * (∫⁻ x, w x * v x ^ 2 ∂μ) := by
      rw [mul_pow, hsquare, hsquare]
      simp

variable {n : ℕ}

/-- `eLpNorm` is translation-invariant on `EuclideanSpace`. -/
lemma eLpNorm_sub_right_eucl {f : EuclideanSpace ℝ (Fin n) → ℂ} (z : EuclideanSpace ℝ (Fin n))
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun x => f (x - z)) 2 volume = eLpNorm f 2 volume := by
  have hm : AEMeasurable (fun x => ‖f x‖ₑ ^ ENNReal.toReal 2) volume := by fun_prop
  have hmp := measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin n))) z
  have hmk := hmp.quasiMeasurePreserving.ae hm.ae_eq_mk
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    lintegral_congr_ae hmk, lintegral_congr_ae hm.ae_eq_mk]
  congr 1
  exact hmp.lintegral_comp hm.measurable_mk

/-- Translation preserves `MemLp` on `EuclideanSpace`. -/
lemma memLp_sub_right_eucl {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : MemLp f 2 volume) (z : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => f (x - z)) 2 volume := by
  refine ⟨hf.1.comp_measurePreserving (measurePreserving_sub_right volume z), ?_⟩
  rw [eLpNorm_sub_right_eucl z hf.1]
  simpa using hf.2

end Young

/-! ## Young's L² convolution inequality on `EuclideanSpace ℝ (Fin n)` -/

section Young2

variable {n : ℕ}

/-- Subtraction is jointly quasi-measure-preserving on `EuclideanSpace`. -/
lemma quasiMeasurePreserving_sub_pair :
    Measure.QuasiMeasurePreserving
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => p.1 - p.2)
      (volume.prod volume) volume :=
  quasiMeasurePreserving_sub volume volume

/-- **Young's convolution inequality (L² case) on `EuclideanSpace ℝ (Fin n)`. -/
theorem young_convolution_inequality_L2_eucl
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hg_int : Integrable g volume) (hf_lp : MemLp f 2 volume) :
    eLpNorm (fun x => ∫ y, g (x - y) • f y ∂volume) 2 volume ≤
      (ENNReal.ofReal (∫ y, |g y| ∂volume)) * eLpNorm f 2 volume := by
  have hlint_shift (y : EuclideanSpace ℝ (Fin n)) :
      ∫⁻ x, ‖g (x - y)‖ₑ ∂volume = ∫⁻ x, ‖g x‖ₑ ∂volume := by
    have hg_comp : Integrable (fun t => g (t - y)) volume :=
      (measurePreserving_sub_right volume y).integrable_comp_of_integrable hg_int
    rw [← ofReal_integral_norm_eq_lintegral_enorm hg_comp,
      ← ofReal_integral_norm_eq_lintegral_enorm hg_int]
    congr 1
    exact integral_sub_right_eq_self (fun t => ‖g t‖) y
  have hlint_shift_left (x : EuclideanSpace ℝ (Fin n)) :
      ∫⁻ y, ‖g (x - y)‖ₑ ∂volume = ∫⁻ y, ‖g y‖ₑ ∂volume := by
    have hg_comp : Integrable (fun t => g (x - t)) volume :=
      (Measure.measurePreserving_sub_left volume x).integrable_comp_of_integrable hg_int
    rw [← ofReal_integral_norm_eq_lintegral_enorm hg_comp,
      ← ofReal_integral_norm_eq_lintegral_enorm hg_int]
    congr 1
    exact integral_sub_left_eq_self (fun t => ‖g t‖) volume x
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2 ≤
        (∫⁻ y, ‖g y‖ₑ ∂volume) *
          (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) := by
    have hg_x : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) => ‖g (x - y)‖ₑ) volume :=
      ((hg_int.aestronglyMeasurable.comp_measurePreserving
        (Measure.measurePreserving_sub_left volume x)).enorm)
    have hf_enorm : AEMeasurable (fun y : EuclideanSpace ℝ (Fin n) => ‖f y‖ₑ) volume :=
      hf_lp.aestronglyMeasurable.enorm
    have hnorm :
        ‖∫ y, g (x - y) • f y ∂volume‖ₑ ≤
          ∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ∂volume := by
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      apply lintegral_congr
      intro y
      rw [Complex.real_smul, enorm_mul]
      congr 1
      rw [← ofReal_norm_eq_enorm (↑(g (x - y)) : ℂ), Complex.norm_real]
      rw [← ofReal_norm_eq_enorm (g (x - y)), Real.norm_eq_abs]
    calc
      ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2
          ≤ (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ∂volume) ^ 2 :=
        pow_le_pow_left₀ (zero_le _) hnorm 2
      _ ≤ (∫⁻ y, ‖g (x - y)‖ₑ ∂volume) *
          (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) :=
        lintegral_weight_mul_sq_le_eucl _ _ hg_x hf_enorm
      _ = (∫⁻ y, ‖g y‖ₑ ∂volume) *
          (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) := by
        congr 1
        exact hlint_shift_left x
  let G : ℝ≥0∞ := ∫⁻ y, ‖g y‖ₑ ∂volume
  let F2 : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂volume
  have hG_top : G ≠ (⊤ : ℝ≥0∞) := hg_int.hasFiniteIntegral.ne
  have h_joint : AEMeasurable
      (Function.uncurry fun x y : EuclideanSpace ℝ (Fin n) =>
        ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2)
      (volume.prod volume) := by
    have hg_joint : AEMeasurable
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => ‖g (z.1 - z.2)‖ₑ)
        (volume.prod volume) := by
      simpa [Function.comp_def] using
        (hg_int.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
          quasiMeasurePreserving_sub_pair)
    exact hg_joint.mul (hf_lp.aestronglyMeasurable.enorm.comp_snd.pow_const _)
  have hdouble :
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2 ∂volume) ≤
        G ^ 2 * F2 := by
    calc
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ 2 ∂volume)
          ≤ ∫⁻ x, G *
              (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume := by
            apply lintegral_mono
            intro x
            exact hpoint x
      _ = G * (∫⁻ x,
              (∫⁻ y, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume) := by
            rw [lintegral_const_mul' G _ hG_top]
      _ = G * (∫⁻ y,
              (∫⁻ x, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume) := by
            rw [lintegral_lintegral_swap h_joint]
      _ = G * (G * F2) := by
            congr 1
            calc
              (∫⁻ y, (∫⁻ x, ‖g (x - y)‖ₑ * ‖f y‖ₑ ^ 2 ∂volume) ∂volume)
                  = ∫⁻ y, G * ‖f y‖ₑ ^ 2 ∂volume := by
                    apply lintegral_congr
                    intro y
                    rw [lintegral_mul_const' _ _ (by rw [← ofReal_norm_eq_enorm (f y), ← ENNReal.ofReal_pow (by positivity)]; exact ENNReal.ofReal_ne_top), hlint_shift _]
              _ = G * F2 := by
                    rw [lintegral_const_mul' G _ hG_top]
      _ = G ^ 2 * F2 := by ring
  have hroot :
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ (2 : ℝ) ∂volume) ^
          (1 / 2 : ℝ) ≤
        G * F2 ^ (1 / 2 : ℝ) := by
    calc
      (∫⁻ x, ‖∫ y, g (x - y) • f y ∂volume‖ₑ ^ (2 : ℝ) ∂volume) ^
            (1 / 2 : ℝ)
          ≤ (G ^ 2 * F2) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (by simpa [ENNReal.rpow_two] using hdouble) (by norm_num)
      _ = G * F2 ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ∫ y, |g y| ∂volume = ∫ y, ‖g y‖ ∂volume from
      integral_congr_ae (Eventually.of_forall fun y => (Real.norm_eq_abs _).symm),
    ofReal_integral_norm_eq_lintegral_enorm hg_int]
  simpa [G, F2] using hroot

end Young2

/-! ## Clause (b): the L² contraction -/

section Contraction

variable {n : ℕ}

/-- (b) For fixed `t > 0`, the heat convolution is an `L²` contraction. -/
theorem heatConvN_eLpNorm_le {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (heatConvN n t f) 2 volume ≤ eLpNorm f 2 volume := by
  have hyoung := young_convolution_inequality_L2_eucl
    (g := heatKernelN n t) (f := f) (heatKernelN_integrable ht) hf
  have habs : ∫ y, |heatKernelN n t y| ∂volume = ∫ y, heatKernelN n t y ∂volume := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    exact abs_of_nonneg (heatKernelN_nonneg ht y)
  have hint : ENNReal.ofReal (∫ y, |heatKernelN n t y| ∂volume) = 1 := by
    rw [habs, heatKernelN_integral ht]
    norm_num
  have hone : ENNReal.ofReal (∫ y, |heatKernelN n t y| ∂volume) * eLpNorm f 2 volume
      = eLpNorm f 2 volume := by
    rw [hint, one_mul]
  refine hyoung.trans_eq ?_
  rw [hone]

end Contraction

/-! ## Integrability helper: product of two `L²` functions -/

section MulL2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma enorm_real_eq (x : ℝ) : ‖x‖ₑ = ENNReal.ofReal |x| := by
  rw [← ofReal_norm_eq_enorm (x), Real.norm_eq_abs]

lemma enorm_nonneg_real_eq {x : ℝ} (h : 0 ≤ x) : ‖x‖ₑ = ENNReal.ofReal x := by
  simp only [enorm_real_eq]
  exact congrArg ENNReal.ofReal (abs_of_nonneg h)

lemma enorm_pow_two (a : ℝ≥0∞) : a ^ ENNReal.toReal 2 = a * a := by
  norm_num
  exact pow_two a

lemma eLpNorm_two_enorm_eq {β : Type*} [NormedAddCommGroup β] (w : α → β) :
    eLpNorm w 2 μ = (∫⁻ x, ‖w x‖ₑ * ‖w x‖ₑ ∂μ) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  apply lintegral_congr
  intro x
  exact enorm_pow_two _

/-- The product of two real `L²` functions is integrable (Cauchy--Schwarz). -/
lemma integrable_mul_of_memLp_two {u v : α → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    Integrable (fun x => u x * v x) μ := by
  refine ⟨hu.aestronglyMeasurable.mul hv.aestronglyMeasurable, ?_⟩
  have hfU : AEMeasurable (fun x => ‖u x‖ₑ) μ := hu.aestronglyMeasurable.enorm
  have hfV : AEMeasurable (fun x => ‖v x‖ₑ) μ := hv.aestronglyMeasurable.enorm
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hfU hfV
  simp only [Pi.mul_apply] at hcs
  have key {γ : Type} [NormedAddCommGroup γ] (w : α → γ) (hw : MemLp w 2 μ) :
      (∫⁻ x, ‖w x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) < ⊤ := by
    refine lt_top_iff_ne_top.2 (fun h => hw.2.ne ?_)
    refine (eLpNorm_two_enorm_eq w).trans ?_
    rw [lintegral_congr (fun x => (enorm_pow_two _).symm)]
    exact h
  rw [show HasFiniteIntegral (fun x => u x * v x) μ =
      (∫⁻ x, ‖u x * v x‖ₑ ∂μ < ⊤) from rfl,
    lintegral_congr (fun x => enorm_mul (u x) (v x))]
  exact lt_of_le_of_lt hcs (ENNReal.mul_lt_top (key u hu) (key v hv))

end MulL2

/-! ## Clause (c): the approximate-identity limit -/

section Limit

variable {n : ℕ}

lemma rpow_half_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

lemma enorm_smul_real_complex (a : ℝ) (w : ℂ) : ‖a • w‖ₑ = ‖a‖ₑ * ‖w‖ₑ := by
  have h1 : ‖(a : ℂ)‖ₑ = ‖a‖ₑ := by
    rw [show ((a : ℂ)) = Complex.ofReal a from rfl, ← ofReal_norm_eq_enorm ((a : ℂ)),
      Complex.norm_real, ← ofReal_norm_eq_enorm (a), Real.norm_eq_abs]
  rw [Complex.real_smul, enorm_mul, h1]

lemma lintegral_ofReal_eq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : 0 ≤ f) (hfi : Integrable f μ) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ENNReal.ofReal (∫ x, f x ∂μ) := by
  have h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ = ∫⁻ x, ‖f x‖ₑ ∂μ := by
    apply lintegral_congr
    intro x
    rw [← ofReal_norm_eq_enorm (f x), Real.norm_eq_abs, abs_of_nonneg (hf x)]
  rw [h1, ← ofReal_integral_norm_eq_lintegral_enorm hfi]
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun x => by
    simp [Real.norm_eq_abs, abs_of_nonneg (hf x)])

/-- Translations are strongly continuous in `L²` on `EuclideanSpace`. -/
theorem eLpNorm_translation_tendsto_eucl
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) :
    Tendsto (fun z => eLpNorm (fun x => f (x - z) - f x) 2 volume) (𝓝 0) (𝓝 0) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let g : EuclideanSpace ℝ (Fin n) → C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)) :=
    fun z => ⟨fun x => x - z, continuous_id.sub continuous_const⟩
  have hg : Continuous g := by
    let G : C(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℝ (Fin n)) :=
      ⟨fun p => p.2 - p.1, continuous_snd.sub continuous_fst⟩
    have hgc : g = (ContinuousMap.curry G : C(EuclideanSpace ℝ (Fin n),
        C(EuclideanSpace ℝ (Fin n), EuclideanSpace ℝ (Fin n)))) := rfl
    rw [hgc]
    exact (ContinuousMap.curry G).continuous
  have hgm : ∀ z, MeasurePreserving (g z) volume volume :=
    fun z => measurePreserving_sub_right volume z
  let F : EuclideanSpace ℝ (Fin n) → Lp ℂ 2 volume := fun z =>
    Lp.compMeasurePreserving (g z) (hgm z) (hf.toLp f)
  have hF : Continuous F := continuous_const.compMeasurePreservingLp hg hgm (by norm_num)
  have hF0 : F 0 = hf.toLp f := by
    dsimp [F]
    rw [Lp.toLp_compMeasurePreserving]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun x => by simp [g]
  have hed : Tendsto (fun z => edist (F z) (hf.toLp f)) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun _ : EuclideanSpace ℝ (Fin n) => hf.toLp f) := continuous_const
    simpa [hF0] using (hF.edist hc).tendsto 0
  convert hed using 1
  ext z
  dsimp [F]
  rw [Lp.toLp_compMeasurePreserving, Lp.edist_toLp_toLp]
  apply eLpNorm_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [g]

lemma heatKernelN_enorm_lintegral {s : ℝ} (hs : 0 < s) :
    ∫⁻ z, ‖heatKernelN n s z‖ₑ ∂volume = 1 := by
  rw [lintegral_congr (fun z => by
    rw [← ofReal_norm_eq_enorm (heatKernelN n s z), Real.norm_eq_abs,
      abs_of_nonneg (heatKernelN_nonneg hs z)])]
  exact heatKernelN_lintegral_eq_one hs

lemma eLpNorm_sub_left_eucl {f : EuclideanSpace ℝ (Fin n) → ℂ} (x : EuclideanSpace ℝ (Fin n))
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm (fun z => f (x - z)) 2 volume = eLpNorm f 2 volume := by
  have hm : AEMeasurable (fun z => ‖f z‖ₑ ^ ENNReal.toReal 2) volume := by fun_prop
  have hmp := Measure.measurePreserving_sub_left volume x
  have hmk := hmp.quasiMeasurePreserving.ae hm.ae_eq_mk
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    lintegral_congr_ae hmk, lintegral_congr_ae hm.ae_eq_mk]
  congr 1
  exact hmp.lintegral_comp hm.measurable_mk

lemma memLp_sub_left_eucl {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : MemLp f 2 volume) (x : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun z => f (x - z)) 2 volume := by
  refine ⟨hf.1.comp_measurePreserving (Measure.measurePreserving_sub_left volume x), ?_⟩
  rw [eLpNorm_sub_left_eucl x hf.1]
  simpa using hf.2

lemma integrable_smul_of_memLp_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : α → ℝ} {w : α → ℂ} (hu : MemLp u 2 μ) (hw : MemLp w 2 μ) :
    Integrable (fun z => u z • w z) μ := by
  have hfU : AEMeasurable (fun x => ‖u x‖ₑ) μ := hu.aestronglyMeasurable.enorm
  have hfW : AEMeasurable (fun x => ‖w x‖ₑ) μ := hw.aestronglyMeasurable.enorm
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hfU hfW
  simp only [Pi.mul_apply] at hcs
  have key : ∀ {γ : Type} [NormedAddCommGroup γ] (v : α → γ), MemLp v 2 μ →
      (∫⁻ x, ‖v x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) < ⊤ :=
    fun v hv => lt_top_iff_ne_top.2 (fun h => hv.2.ne (by
      refine (eLpNorm_two_enorm_eq v).trans ?_
      rw [lintegral_congr (fun x => (enorm_pow_two _).symm)]
      exact h))
  have hsm : (fun z => u z • w z) = fun z => (u z : ℂ) * w z :=
    funext fun z => by rw [Complex.real_smul]
  have hAE : AEMeasurable (fun z => (u z : ℂ) * w z) μ :=
    (hu.aestronglyMeasurable.aemeasurable.complex_ofReal).mul
      hw.aestronglyMeasurable.aemeasurable
  refine ⟨hAE.aestronglyMeasurable.congr (Eventually.of_forall fun z => congrFun hsm z), ?_⟩
  have hbnd : ∫⁻ z, ‖u z • w z‖ₑ ∂μ ≤ ∫⁻ z, ‖u z‖ₑ * ‖w z‖ₑ ∂μ :=
    lintegral_mono fun z => le_of_eq (enorm_smul_real_complex _ _)
  exact lt_of_le_of_lt hbnd (lt_of_le_of_lt hcs (ENNReal.mul_lt_top (key u hu) (key w hw)))

end Limit

lemma integrable_smul_const_complex {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} {c : ℂ} (hg : Integrable g μ) :
    Integrable (fun z => g z • c) μ := by
  have hAE : AEMeasurable (fun z => (g z : ℂ) * c) μ :=
    (hg.aestronglyMeasurable.aemeasurable.complex_ofReal).mul aemeasurable_const
  have hsm : (fun z => g z • c) = fun z => (g z : ℂ) * c :=
    funext fun z => by rw [Complex.real_smul]
  refine ⟨hAE.aestronglyMeasurable.congr (Eventually.of_forall fun z => congrFun hsm z), ?_⟩
  rw [show HasFiniteIntegral (fun z => g z • c) μ =
      (∫⁻ z, ‖g z • c‖ₑ ∂μ < ⊤) from rfl,
    lintegral_congr (fun z => enorm_smul_real_complex _ _),
    lintegral_mul_const' _ _ (by simp)]
  exact ENNReal.mul_lt_top hg.hasFiniteIntegral (by simp)

lemma heatKernelN_memLp_two {s : ℝ} (hs : 0 < s) :
    MemLp (heatKernelN n s) 2 volume := by
  have hint' : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      Real.exp (-‖z‖ ^ 2 / (4 * (s / 2)))) volume :=
    integrable_exp_neg_norm_sq (by positivity)
  have hint : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
      ((4 * π * s) ^ (-(n : ℝ) / 2)) ^ 2 *
        Real.exp (-‖z‖ ^ 2 / (4 * (s / 2)))) volume := hint'.const_mul _
  have hsq : ∀ z : EuclideanSpace ℝ (Fin n),
      heatKernelN n s z * heatKernelN n s z
        = ((4 * π * s) ^ (-(n : ℝ) / 2)) ^ 2 * Real.exp (-‖z‖ ^ 2 / (4 * (s / 2))) := by
    intro z
    unfold heatKernelN
    have hEE : Real.exp (-‖z‖ ^ 2 / (4 * s)) * Real.exp (-‖z‖ ^ 2 / (4 * s))
        = Real.exp (-‖z‖ ^ 2 / (4 * (s / 2))) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    calc (4 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * s))
          * ((4 * π * s) ^ (-(n : ℝ) / 2) * Real.exp (-‖z‖ ^ 2 / (4 * s)))
        = ((4 * π * s) ^ (-(n : ℝ) / 2)) * ((4 * π * s) ^ (-(n : ℝ) / 2))
          * (Real.exp (-‖z‖ ^ 2 / (4 * s)) * Real.exp (-‖z‖ ^ 2 / (4 * s))) := by ring
      _ = ((4 * π * s) ^ (-(n : ℝ) / 2)) * ((4 * π * s) ^ (-(n : ℝ) / 2))
          * Real.exp (-‖z‖ ^ 2 / (4 * (s / 2))) := by rw [hEE]
      _ = ((4 * π * s) ^ (-(n : ℝ) / 2)) ^ 2 * Real.exp (-‖z‖ ^ 2 / (4 * (s / 2))) := by
          rw [← pow_two]
  have heq : ∫⁻ z, ‖heatKernelN n s z‖ₑ * ‖heatKernelN n s z‖ₑ ∂volume
      = ENNReal.ofReal (((4 * π * s) ^ (-(n : ℝ) / 2)) ^ 2 *
        ((4 * π * (s / 2)) ^ ((1 : ℝ) / 2)) ^ n) := by
    have h1 : ∀ z : EuclideanSpace ℝ (Fin n),
        ‖heatKernelN n s z‖ₑ * ‖heatKernelN n s z‖ₑ
          = ENNReal.ofReal (((4 * π * s) ^ (-(n : ℝ) / 2)) ^ 2 *
            Real.exp (-‖z‖ ^ 2 / (4 * (s / 2)))) := by
      intro z
      have hA : ‖heatKernelN n s z‖ₑ * ‖heatKernelN n s z‖ₑ
          = ENNReal.ofReal (heatKernelN n s z) * ENNReal.ofReal (heatKernelN n s z) :=
        by rw [enorm_nonneg_real_eq (heatKernelN_nonneg hs z)]
      rw [hA, ← ENNReal.ofReal_mul (heatKernelN_nonneg hs z), hsq z]
    rw [lintegral_congr (fun z => h1 z),
      lintegral_ofReal_eq_integral
        (fun z => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le) hint,
      integral_const_mul,
      integral_exp_neg_norm_sq (by positivity : (0:ℝ) < s / 2)]
  refine ⟨(heatKernelN_integrable hs).aestronglyMeasurable, ?_⟩
  rw [lt_top_iff_ne_top, eLpNorm_two_enorm_eq]
  intro htop
  rw [heq] at htop
  exact absurd htop (by simp)

lemma heatConvN_sub_eq {s : ℝ} (hs : 0 < s) {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : MemLp f 2 volume) (x : EuclideanSpace ℝ (Fin n)) :
    heatConvN n s f x - f x
      = ∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume := by
  have hint1 : Integrable (fun z => heatKernelN n s z • f (x - z)) volume :=
    integrable_smul_of_memLp_two (heatKernelN_memLp_two hs) (memLp_sub_left_eucl hf x)
  have hint2 : Integrable (fun z => heatKernelN n s z • f x) volume :=
    integrable_smul_const_complex (heatKernelN_integrable hs)
  have hconv : heatConvN n s f x
      = ∫ z, heatKernelN n s z • f (x - z) ∂volume := by
    unfold heatConvN
    have hfun : (fun y => heatKernelN n s (x - y) • f y)
        = fun y => (fun z => heatKernelN n s z • f (x - z)) (x - y) := by
      funext y
      show heatKernelN n s (x - y) • f y
        = heatKernelN n s (x - y) • f (x - (x - y))
      rw [sub_sub_cancel]
    rw [hfun, integral_sub_left_eq_self (fun z => heatKernelN n s z • f (x - z)) volume x]
  have hconst : f x = ∫ z, heatKernelN n s z • f x ∂volume := by
    rw [show ∫ z, heatKernelN n s z • f x ∂volume
        = ((∫ z, heatKernelN n s z ∂volume) • f x) from integral_smul_const _ _,
      heatKernelN_integral hs]
    simp
  have e1 : heatConvN n s f x - f x
      = (∫ z, heatKernelN n s z • f (x - z) ∂volume) - f x := by rw [hconv]
  have e2 : (∫ z, heatKernelN n s z • f (x - z) ∂volume) - f x
      = (∫ z, heatKernelN n s z • f (x - z) ∂volume)
        - (∫ z, heatKernelN n s z • f x ∂volume) := by rw [← hconst]
  have e3 : (∫ z, heatKernelN n s z • f (x - z) ∂volume)
      - (∫ z, heatKernelN n s z • f x ∂volume)
      = ∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume := by
    rw [← integral_sub hint1 hint2]
    exact integral_congr_ae (Eventually.of_forall fun z => by
      exact (smul_sub (heatKernelN n s z) (f (x - z)) (f x)).symm)
  exact e1.trans (e2.trans e3)

/-! ## The reformed theorem -/

section Main

variable {n : ℕ}

/-- The translation-error norm is at most `2 ‖f‖₂`. -/
lemma eLpNorm_translation_sub_le_two
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume)
    (z : EuclideanSpace ℝ (Fin n)) :
    eLpNorm (fun x => f (x - z) - f x) 2 volume ≤ 2 * eLpNorm f 2 volume := by
  have hle := eLpNorm_sub_le
    (hf.1.comp_measurePreserving (measurePreserving_sub_right volume z))
    hf.1 (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hle' : eLpNorm (fun x => f (x - z) - f x) 2 volume ≤
      eLpNorm (fun x => f (x - z)) 2 volume + eLpNorm f 2 volume := hle
  rw [eLpNorm_sub_right_eucl z hf.1, ← two_mul] at hle'
  exact hle'

/-- The translation-error `L²` norm is finite for every translation. -/
lemma eLpNorm_translation_sub_ne_top
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume)
    (z : EuclideanSpace ℝ (Fin n)) :
    eLpNorm (fun x => f (x - z) - f x) 2 volume ≠ ⊤ :=
  ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (by norm_num) hf.2.ne) (eLpNorm_translation_sub_le_two hf z)

/-- Squared translation-error norm as an `x`-integral. -/
lemma eLpNorm_translation_sub_sq
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (z : EuclideanSpace ℝ (Fin n)) :
    (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2
      = ∫⁻ x, ‖f (x - z) - f x‖ₑ ^ 2 ∂volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) from by norm_num, rpow_half_sq]
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_two]

/-- Weighted Cauchy–Schwarz bound for the approximate-identity error:
the `s`-error norm is at most the square root of the `G_s`-weighted average of the
squared translation-error norms. -/
lemma eLpNorm_heatConvN_sub_le {s : ℝ} (hs : 0 < s)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) :
    eLpNorm (fun x => heatConvN n s f x - f x) 2 volume ≤
      (∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
        (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume) ^ (1 / 2 : ℝ) := by
  -- pointwise bound on the mollified difference
  have hGmeas : AEMeasurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (heatKernelN n s z)) volume :=
    ENNReal.measurable_ofReal.comp_aemeasurable (heatKernelN_integrable hs).aemeasurable
  have hfw_meas : ∀ x : EuclideanSpace ℝ (Fin n),
      AEMeasurable (fun z => ‖f (x - z) - f x‖ₑ) volume := fun x => by
    have h : AEMeasurable (fun z => ‖f (x - z) - f x‖ₑ) volume :=
      ((hf.1.comp_measurePreserving
        (Measure.measurePreserving_sub_left volume x)).sub
          (aestronglyMeasurable_const (b := f x))).enorm
    simpa [Function.comp_def] using h
  have hpoint (x : EuclideanSpace ℝ (Fin n)) :
      ‖∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume‖ₑ ^ 2 ≤
        ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * ‖f (x - z) - f x‖ₑ ^ 2 ∂volume := by
    have hnorm : ‖∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume‖ₑ
        ≤ ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * ‖f (x - z) - f x‖ₑ ∂volume := by
      refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
      apply lintegral_congr
      intro z
      rw [Complex.real_smul, enorm_mul]
      congr 1
      rw [← ofReal_norm_eq_enorm]
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (heatKernelN_nonneg hs z)]
    calc
      ‖∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume‖ₑ ^ 2
          ≤ (∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * ‖f (x - z) - f x‖ₑ ∂volume) ^ 2 :=
        pow_le_pow_left₀ (zero_le _) hnorm 2
      _ ≤ (∫⁻ z, ENNReal.ofReal (heatKernelN n s z) ∂volume) *
            (∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * ‖f (x - z) - f x‖ₑ ^ 2 ∂volume) :=
        lintegral_weight_mul_sq_le_eucl _ _ hGmeas (hfw_meas x)
      _ = ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * ‖f (x - z) - f x‖ₑ ^ 2 ∂volume := by
        rw [heatKernelN_lintegral_eq_one hs, one_mul]
  -- joint measurability for Fubini
  have hjoint : AEMeasurable (Function.uncurry fun x z : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (heatKernelN n s z) * ‖f (x - z) - f x‖ₑ ^ 2)
      (volume.prod volume) := by
    have hG2 : AEMeasurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal (heatKernelN n s p.2)) (volume.prod volume) :=
      ENNReal.measurable_ofReal.comp_aemeasurable
        ((heatKernelN_integrable hs).aemeasurable.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd)
    have hf1 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f (p.1 - p.2))
        (volume.prod volume) :=
      hf.1.comp_quasiMeasurePreserving quasiMeasurePreserving_sub_pair
    have hf2 : AEStronglyMeasurable
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => f p.1)
        (volume.prod volume) :=
      hf.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
    exact hG2.mul ((hf1.sub hf2).enorm.pow_const _)
  -- double-integral bound
  have hdouble :
      (∫⁻ x, ‖∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume‖ₑ ^ 2 ∂volume) ≤
        ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
          (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume := by
    calc
      (∫⁻ x, ‖∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume‖ₑ ^ 2 ∂volume)
          ≤ ∫⁻ x, (∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
              ‖f (x - z) - f x‖ₑ ^ 2 ∂volume) ∂volume :=
        lintegral_mono fun x => hpoint x
      _ = ∫⁻ z, (∫⁻ x, ENNReal.ofReal (heatKernelN n s z) *
            ‖f (x - z) - f x‖ₑ ^ 2 ∂volume) ∂volume :=
        lintegral_lintegral_swap hjoint
      _ = ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
            (∫⁻ x, ‖f (x - z) - f x‖ₑ ^ 2 ∂volume) ∂volume := by
        apply lintegral_congr
        intro z
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
            (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume := by
        apply lintegral_congr
        intro z
        rw [eLpNorm_translation_sub_sq z]
  -- conclude via the square root
  have htarget : (∫⁻ x, ‖heatConvN n s f x - f x‖ₑ ^ (ENNReal.toReal 2) ∂volume)
      ≤ ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
          (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume := by
    have hcongr : (fun x => ‖heatConvN n s f x - f x‖ₑ ^ (ENNReal.toReal 2))
        = fun x => ‖∫ z, heatKernelN n s z • (f (x - z) - f x) ∂volume‖ₑ ^ 2 := by
      funext x
      rw [heatConvN_sub_eq hs hf x,
        show ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) from by norm_num, ENNReal.rpow_two]
    rw [hcongr]
    exact hdouble
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show ENNReal.toReal (2 : ℝ≥0∞) = (2 : ℝ) from by norm_num]
  exact ENNReal.rpow_le_rpow htarget (by norm_num)

/-- Clause (a): `heatConvN n t f` is smooth in `x` for `t > 0`. -/
lemma heatKernelN_contDiff {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ ∞ (heatKernelN n t) := by
  unfold heatKernelN
  simp_rw [euclidean_norm_sq]
  fun_prop

lemma heatKernelN_sub_contDiff {t : ℝ} (ht : 0 < t)
    (y : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ ∞ (fun x => heatKernelN n t (x - y)) := by
  exact (heatKernelN_contDiff ht).comp (contDiff_id.sub contDiff_const)

lemma heatKernelN_iteratedFDeriv_continuous {t : ℝ} (ht : 0 < t) (j : ℕ) :
    Continuous (iteratedFDeriv ℝ j (heatKernelN n t)) := by
  exact (heatKernelN_contDiff ht).continuous_iteratedFDeriv (by exact_mod_cast le_top)

lemma heatKernelN_iteratedFDeriv_zero_gaussian_bound {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, ∀ z : EuclideanSpace ℝ (Fin n),
      ‖iteratedFDeriv ℝ 0 (heatKernelN n t) z‖ ≤
        C * Real.exp (-‖z‖ ^ 2 / (8 * t)) := by
  refine ⟨(4 * π * t) ^ (-(n : ℝ) / 2), fun z => ?_⟩
  rw [norm_iteratedFDeriv_zero]
  unfold heatKernelN
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg (by positivity) _)
  have hz : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
  have ht8 : 0 < 8 * t := by positivity
  have ht4 : 0 < 4 * t := by positivity
  apply (div_le_div_iff_of_pos_right ht8).mp
  rw [div_div]
  field_simp
  linarith

/-- Smooth functions all of whose derivatives have a fixed Gaussian majorant.
This class is arranged so that it is closed under taking the Fréchet derivative. -/
def HasGaussianDerivBounds (t : ℝ)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : EuclideanSpace ℝ (Fin n) → F) : Prop :=
  ContDiff ℝ ∞ g ∧ ∀ j : ℕ, ∃ C : ℝ, ∀ z,
    ‖iteratedFDeriv ℝ j g z‖ ≤ C * Real.exp (-‖z‖ ^ 2 / (8 * t))

lemma HasGaussianDerivBounds.fderiv {t : ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : HasGaussianDerivBounds t g) :
    HasGaussianDerivBounds t (fderiv ℝ g) := by
  constructor
  · exact (contDiff_infty_iff_fderiv.mp hg.1).2
  · intro j
    obtain ⟨C, hC⟩ := hg.2 (j + 1)
    exact ⟨C, fun z => by simpa [norm_iteratedFDeriv_fderiv] using hC z⟩

lemma norm_iteratedFDeriv_exp (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j Real.exp x‖ = Real.exp x := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrFun (iteratedDeriv_exp_const_mul j 1) x
  simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos x)] using congrArg norm h

lemma heatQuadratic_base_one_le {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) :
    1 ≤ 1 + (1 + ‖z‖) / t := by
  have : 0 ≤ (1 + ‖z‖) / t := div_nonneg (by positivity) ht.le
  linarith

lemma norm_fderiv_heatQuadratic {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (fun w : EuclideanSpace ℝ (Fin n) => -‖w‖ ^ 2 / (4 * t)) z‖
      = ‖z‖ / (2 * t) := by
  rw [show (fun w : EuclideanSpace ℝ (Fin n) => -‖w‖ ^ 2 / (4 * t)) =
      fun w => (-1 / (4 * t)) * ‖w‖ ^ 2 by funext w; ring]
  rw [fderiv_const_mul (hasStrictFDerivAt_norm_sq z).differentiableAt,
    fderiv_norm_sq_apply]
  rw [show (2 • innerSL ℝ z) = (2 : ℝ) • innerSL ℝ z by
      simp [two_nsmul, two_smul], norm_smul, norm_smul, innerSL_apply_norm]
  rw [Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), Real.norm_eq_abs]
  rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))]
  field_simp
  ring

lemma norm_iteratedFDeriv_clm_eq_zero
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (j : ℕ) (hj : 2 ≤ j) (x : E) :
    ‖iteratedFDeriv ℝ j L x‖ = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 2 + k = (1 + k) + 1 by omega, ← norm_iteratedFDeriv_fderiv]
  have hf : fderiv ℝ (L : E → F) = fun _ => L := by
    funext y
    exact L.fderiv
  rw [hf]
  simp [iteratedFDeriv_const_of_ne]

/-- Multiples of the real inner product, as an honest (linear, not semilinear)
bilinear map. -/
noncomputable def heatInnerCLM {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂ (c • innerₗ E) |c| (fun x y => by
    simpa [abs_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (abs_real_inner_le_norm x y) (abs_nonneg c))

lemma heatInnerCLM_apply {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (x y : E) : heatInnerCLM c x y = c * inner ℝ x y := rfl

lemma norm_heatInnerCLM_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) : ‖(heatInnerCLM c : E →L[ℝ] E →L[ℝ] ℝ)‖ ≤ |c| :=
  LinearMap.mkContinuous₂_norm_le _ (abs_nonneg c) _

lemma fderiv_quadratic_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (t : ℝ) :
    fderiv ℝ (fun w : E => -‖w‖ ^ 2 / (4 * t)) = ⇑(heatInnerCLM (-1 / (2 * t)) : E →L[ℝ] E →L[ℝ] ℝ) := by
  funext z
  rw [show (fun w : E => -‖w‖ ^ 2 / (4 * t)) =
      fun w => (-1 / (4 * t)) * ‖w‖ ^ 2 by funext w; ring]
  rw [fderiv_const_mul (hasStrictFDerivAt_norm_sq z).differentiableAt]
  ext v
  simp only [ContinuousLinearMap.smul_apply, fderiv_norm_sq_apply, heatInnerCLM_apply,
    smul_eq_mul, nsmul_eq_mul, innerSL_apply_apply]
  push_cast
  by_cases ht : t = 0
  · simp [ht]
  · field_simp
    ring

lemma norm_iteratedFDeriv_of_fderiv_clm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : E → F} {L : E →L[ℝ] E →L[ℝ] F} (h : fderiv ℝ q = ⇑L) (k : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ (k + 2) q z‖ ≤ ‖L‖ := by
  rw [show k + 2 = (k + 1) + 1 by omega, ← norm_iteratedFDeriv_fderiv, h]
  rcases k with _ | k
  · rw [norm_iteratedFDeriv_one, L.fderiv]
  · rw [norm_iteratedFDeriv_clm_eq_zero L (k + 1 + 1) (by omega) z]
    exact norm_nonneg L

lemma norm_iteratedFDeriv_heatQuadratic_le {t : ℝ} (ht : 0 < t)
    (j : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hj : 1 ≤ j) :
    ‖iteratedFDeriv ℝ j
        (fun w : EuclideanSpace ℝ (Fin n) => -‖w‖ ^ 2 / (4 * t)) z‖
      ≤ (1 + (1 + ‖z‖) / t) ^ j := by
  set b : ℝ := 1 + (1 + ‖z‖) / t with hb
  have hb1 : 1 ≤ b := heatQuadratic_base_one_le ht z
  have hzn : 0 ≤ ‖z‖ := norm_nonneg z
  have hbt : 1 / t ≤ b := by
    have h1 : 1 / t ≤ (1 + ‖z‖) / t := by gcongr; linarith
    linarith
  have hbz : ‖z‖ / (2 * t) ≤ b := by
    have h1 : ‖z‖ / (2 * t) ≤ (1 + ‖z‖) / t := by
      rw [div_le_div_iff₀ (by positivity) ht]
      nlinarith
    linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  rcases k with _ | k
  · have h1 := norm_fderiv_heatQuadratic ht z
    simpa [norm_iteratedFDeriv_one, h1] using hbz
  · have h2 := norm_iteratedFDeriv_of_fderiv_clm
      (fderiv_quadratic_eq (E := EuclideanSpace ℝ (Fin n)) t) k z
    have h3 := norm_heatInnerCLM_le (E := EuclideanSpace ℝ (Fin n)) (-1 / (2 * t))
    have h4 : |(-1 / (2 * t))| = 1 / (2 * t) := by
      rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity : 0 < 2 * t)]
    have h5 : 1 / (2 * t) ≤ 1 / t := one_div_le_one_div_of_le ht (by linarith)
    have h6 : b ≤ b ^ (1 + (k + 1)) :=
      le_self_pow₀ hb1 (by omega)
    rw [show 1 + (k + 1) = k + 2 by omega] at h6 ⊢
    rw [h4] at h3
    linarith

lemma poly_gaussian_bound {t : ℝ} (ht : 0 < t) (j : ℕ) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r →
      (1 + (1 + r) / t) ^ j * Real.exp (-r ^ 2 / (8 * t)) ≤ C := by
  refine ⟨(1 + 1 / t) ^ j * Real.exp (2 * t * (j : ℝ) ^ 2), ?_⟩
  intro r hr
  have hA : 0 ≤ 1 + 1 / t := by positivity
  have hbase : 1 + (1 + r) / t ≤ (1 + 1 / t) * (1 + r) := by
    field_simp
    nlinarith
  have hone : 1 + r ≤ Real.exp r := by simpa [add_comm] using Real.add_one_le_exp r
  have hquad : (j : ℝ) * r - r ^ 2 / (8 * t) ≤ 2 * t * (j : ℝ) ^ 2 := by
    field_simp
    nlinarith [sq_nonneg (r - 4 * t * (j : ℝ))]
  calc
    (1 + (1 + r) / t) ^ j * Real.exp (-r ^ 2 / (8 * t))
        ≤ ((1 + 1 / t) * (1 + r)) ^ j * Real.exp (-r ^ 2 / (8 * t)) := by
          gcongr
    _ ≤ ((1 + 1 / t) * Real.exp r) ^ j * Real.exp (-r ^ 2 / (8 * t)) := by
          gcongr
    _ = (1 + 1 / t) ^ j * Real.exp ((j : ℝ) * r - r ^ 2 / (8 * t)) := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring
    _ ≤ (1 + 1 / t) ^ j * Real.exp (2 * t * (j : ℝ) ^ 2) := by
          gcongr

lemma heatKernelN_hasGaussianDerivBounds {t : ℝ} (ht : 0 < t) :
    HasGaussianDerivBounds t (heatKernelN n t) := by
  constructor
  · exact heatKernelN_contDiff ht
  · intro j
    obtain ⟨C, hC⟩ := poly_gaussian_bound ht j
    let A : ℝ := (4 * π * t) ^ (-(n : ℝ) / 2)
    let q : EuclideanSpace ℝ (Fin n) → ℝ := fun z => -‖z‖ ^ 2 / (4 * t)
    refine ⟨|A| * (j.factorial : ℝ) * C, fun z => ?_⟩
    have hq : ContDiff ℝ ∞ q := by
      dsimp [q]
      simp_rw [euclidean_norm_sq]
      fun_prop
    have hc := norm_iteratedFDeriv_comp_le (g := Real.exp) (f := q) (n := j)
      contDiff_exp hq (by exact_mod_cast le_top) z
      (C := Real.exp (q z)) (D := 1 + (1 + ‖z‖) / t)
      (fun i hi => by rw [norm_iteratedFDeriv_exp])
      (fun i hi1 hij => norm_iteratedFDeriv_heatQuadratic_le ht i z hi1)
    have hfun : heatKernelN n t = fun z => A • (Real.exp ∘ q) z := by
      funext w
      simp [heatKernelN, A, q, Function.comp_def, smul_eq_mul]
    rw [hfun, iteratedFDeriv_const_smul_apply'
      (((contDiff_exp.comp hq).of_le (by exact_mod_cast le_top)).contDiffAt),
      norm_smul, Real.norm_eq_abs]
    have hsplit : Real.exp (q z) =
        Real.exp (-‖z‖ ^ 2 / (8 * t)) * Real.exp (-‖z‖ ^ 2 / (8 * t)) := by
      rw [← Real.exp_add]
      dsimp [q]
      congr 1
      field_simp
      ring
    have hpoly := hC ‖z‖ (norm_nonneg z)
    rw [hsplit] at hc
    calc
      |A| * ‖iteratedFDeriv ℝ j (Real.exp ∘ q) z‖
          ≤ |A| * ((j.factorial : ℝ) *
              (Real.exp (-‖z‖ ^ 2 / (8 * t)) * Real.exp (-‖z‖ ^ 2 / (8 * t))) *
              (1 + (1 + ‖z‖) / t) ^ j) := by gcongr
      _ = (|A| * (j.factorial : ℝ) * Real.exp (-‖z‖ ^ 2 / (8 * t))) *
            ((1 + (1 + ‖z‖) / t) ^ j * Real.exp (-‖z‖ ^ 2 / (8 * t))) := by ring
      _ ≤ (|A| * (j.factorial : ℝ) * Real.exp (-‖z‖ ^ 2 / (8 * t))) * C :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = (|A| * (j.factorial : ℝ) * C) * Real.exp (-‖z‖ ^ 2 / (8 * t)) := by ring

lemma integrable_gaussian_mul_norm_of_memLp_two {c : ℝ} (hc : 0 < c)
    (x₀ : EuclideanSpace ℝ (Fin n))
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) :
    Integrable (fun y => Real.exp (-c * ‖x₀ - y‖ ^ 2) * ‖f y‖) volume := by
  let u : EuclideanSpace ℝ (Fin n) → ℝ := fun y => Real.exp (-c * ‖x₀ - y‖ ^ 2)
  have hu_meas : AEStronglyMeasurable u volume := by
    apply Continuous.aestronglyMeasurable
    dsimp [u]
    fun_prop
  have hs : Integrable (fun y : EuclideanSpace ℝ (Fin n) => u y ^ 2) volume := by
    have hbase : Integrable (fun z : EuclideanSpace ℝ (Fin n) =>
        Real.exp (-‖z‖ ^ 2 / (4 * (1 / (8 * c))))) volume :=
      integrable_exp_neg_norm_sq (by positivity)
    have hshift := (Measure.measurePreserving_sub_left volume x₀).integrable_comp_of_integrable hbase
    apply hshift.congr
    filter_upwards with y
    dsimp [u]
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  have hu : MemLp u 2 volume := (memLp_two_iff_integrable_sq hu_meas).2 hs
  exact integrable_mul_of_memLp_two hu hf.norm

def gaussianConv
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : F →L[ℝ] ℂ →L[ℝ] G) (g : EuclideanSpace ℝ (Fin n) → F)
    (f : EuclideanSpace ℝ (Fin n) → ℂ) (x : EuclideanSpace ℝ (Fin n)) : G :=
  ∫ y, B (g (x - y)) (f y) ∂volume

noncomputable def gaussianConvDerivBilinear
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : F →L[ℝ] ℂ →L[ℝ] G) :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] F) →L[ℝ]
      ℂ →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] G) :=
  ((ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin n)) F G) ∘L B.flip).flip

@[simp] lemma gaussianConvDerivBilinear_apply
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : F →L[ℝ] ℂ →L[ℝ] G) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] F)
    (c : ℂ) (v : EuclideanSpace ℝ (Fin n)) :
    gaussianConvDerivBilinear B A c v = B (A v) c := by
  rfl

lemma norm_gaussianConvDerivBilinear_apply_le
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : F →L[ℝ] ℂ →L[ℝ] G) (A : EuclideanSpace ℝ (Fin n) →L[ℝ] F)
    (c : ℂ) :
    ‖gaussianConvDerivBilinear B A c‖ ≤ ‖B‖ * ‖A‖ * ‖c‖ := by
  apply (gaussianConvDerivBilinear B A c).opNorm_le_bound (by positivity)
  intro v
  rw [gaussianConvDerivBilinear_apply]
  calc
    ‖B (A v) c‖ ≤ ‖B (A v)‖ * ‖c‖ := (B (A v)).le_opNorm c
    _ ≤ (‖B‖ * ‖A v‖) * ‖c‖ := by gcongr; exact B.le_opNorm (A v)
    _ ≤ (‖B‖ * (‖A‖ * ‖v‖)) * ‖c‖ := by gcongr; exact A.le_opNorm v
    _ = (‖B‖ * ‖A‖ * ‖c‖) * ‖v‖ := by ring

lemma exp_shift_le {t : ℝ} (ht : 0 < t)
    {x x₀ y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball x₀ 1) :
    Real.exp (-‖x - y‖ ^ 2 / (8 * t)) ≤
      Real.exp (1 / (8 * t)) * Real.exp (-‖x₀ - y‖ ^ 2 / (16 * t)) := by
  have hb : ‖x₀ - x‖ < 1 := by simpa [dist_eq_norm, norm_sub_rev] using hx
  have htri : ‖x₀ - y‖ ≤ ‖x₀ - x‖ + ‖x - y‖ := by
    rw [show x₀ - y = (x₀ - x) + (x - y) by abel]
    exact norm_add_le _ _
  have hsq : ‖x₀ - y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 := by
    have hnon : 0 ≤ ‖x₀ - y‖ := norm_nonneg _
    have ha : 0 ≤ ‖x₀ - x‖ := norm_nonneg _
    have hb' : 0 ≤ ‖x - y‖ := norm_nonneg _
    have hs := sq_nonneg (‖x₀ - x‖ - ‖x - y‖)
    nlinarith
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have ht16 : 0 < 16 * t := by positivity
  apply (div_le_div_iff_of_pos_right ht16).mp
  field_simp
  nlinarith

lemma hasFDerivAt_gaussianConv_integrand
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : Differentiable ℝ g)
    (B : F →L[ℝ] ℂ →L[ℝ] G) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt (fun x => B (g (x - y)) (f y))
      (gaussianConvDerivBilinear B (fderiv ℝ g (x - y)) (f y)) x := by
  have hsub : HasFDerivAt (fun x => x - y) (1 : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) x := by
    simpa using (hasFDerivAt_id x).sub_const y
  have hg' := (hg (x - y)).hasFDerivAt.comp x hsub
  have h := (B.flip (f y)).hasFDerivAt.comp x hg'
  convert h using 1

lemma gaussianConv_integrand_aesm
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : F →L[ℝ] ℂ →L[ℝ] G)
    {g : EuclideanSpace ℝ (Fin n) → F} (hg : Continuous g)
    {f : EuclideanSpace ℝ (Fin n) → ℂ}
    (hf : AEStronglyMeasurable f (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (x : EuclideanSpace ℝ (Fin n)) :
    AEStronglyMeasurable (fun y => B (g (x - y)) (f y))
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  B.aestronglyMeasurable_comp₂
    (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable hf

lemma gaussianConv_bound_aux {t : ℝ} (ht : 0 < t)
    {x x₀ y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Metric.ball x₀ 1)
    {b a K c : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hc : 0 ≤ c)
    (ha : a ≤ K * Real.exp (-‖x - y‖ ^ 2 / (8 * t))) :
    b * a * c ≤ (b * K * Real.exp (1 / (8 * t))) *
      (Real.exp (-(1 / (16 * t)) * ‖x₀ - y‖ ^ 2) * c) := by
  have h := exp_shift_le ht (x := x) (x₀ := x₀) (y := y) hx
  have e : -‖x₀ - y‖ ^ 2 / (16 * t) = -(1 / (16 * t)) * ‖x₀ - y‖ ^ 2 := by ring
  rw [e] at h
  have h2 : a ≤ K * (Real.exp (1 / (8 * t)) *
      Real.exp (-(1 / (16 * t)) * ‖x₀ - y‖ ^ 2)) :=
    ha.trans (mul_le_mul_of_nonneg_left h hK)
  calc b * a * c ≤ b * (K * (Real.exp (1 / (8 * t)) *
        Real.exp (-(1 / (16 * t)) * ‖x₀ - y‖ ^ 2))) * c := by gcongr
    _ = _ := by ring

lemma hasFDerivAt_gaussian_convolution
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → F}
    (hg : HasGaussianDerivBounds t g)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume)
    (B : F →L[ℝ] ℂ →L[ℝ] G)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    HasFDerivAt
      (gaussianConv B g f)
      (gaussianConv (gaussianConvDerivBilinear B) (fderiv ℝ g) f x₀)
      x₀ := by
  obtain ⟨C₀, hC₀⟩ := hg.2 0
  obtain ⟨C₁, hC₁⟩ := hg.2 1
  have hgd : Differentiable ℝ g := hg.1.differentiable (by simp)
  have hgc : Continuous g := hg.1.continuous
  have hdc : Continuous (fderiv ℝ g) := hg.1.continuous_fderiv (by simp)
  have hc : 0 < 1 / (16 * t) := by positivity
  have hint := integrable_gaussian_mul_norm_of_memLp_two hc x₀ hf
  have hx₀ : x₀ ∈ Metric.ball x₀ 1 := Metric.mem_ball_self one_pos
  have hbd₀ (y : EuclideanSpace ℝ (Fin n)) :
      ‖B (g (x₀ - y)) (f y)‖ ≤ (‖B‖ * |C₀| * Real.exp (1 / (8 * t))) *
        (Real.exp (-(1 / (16 * t)) * ‖x₀ - y‖ ^ 2) * ‖f y‖) := by
    refine (B.le_opNorm₂ _ _).trans ?_
    refine gaussianConv_bound_aux ht hx₀ B.opNorm_nonneg (abs_nonneg _) (norm_nonneg _) ?_
    have h := hC₀ (x₀ - y)
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  have hint₀ : Integrable (fun y => B (g (x₀ - y)) (f y)) volume :=
    (hint.const_mul _).mono' (gaussianConv_integrand_aesm B hgc hf.aestronglyMeasurable x₀)
      (ae_of_all _ hbd₀)
  let B' : (EuclideanSpace ℝ (Fin n) →L[ℝ] F) →L[ℝ] ℂ →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] G) := gaussianConvDerivBilinear B
  have hmeas' := gaussianConv_integrand_aesm (F := EuclideanSpace ℝ (Fin n) →L[ℝ] F) (G := EuclideanSpace ℝ (Fin n) →L[ℝ] G)
    B' hdc hf.aestronglyMeasurable x₀
  have hbound : Integrable (fun y => (‖B‖ * |C₁| * Real.exp (1 / (8 * t))) *
      (Real.exp (-(1 / (16 * t)) * ‖x₀ - y‖ ^ 2) * ‖f y‖)) volume := hint.const_mul _
  have hle (y x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball x₀ 1) :
      ‖gaussianConvDerivBilinear B (fderiv ℝ g (x - y)) (f y)‖ ≤
        (‖B‖ * |C₁| * Real.exp (1 / (8 * t))) *
          (Real.exp (-(1 / (16 * t)) * ‖x₀ - y‖ ^ 2) * ‖f y‖) := by
    refine (norm_gaussianConvDerivBilinear_apply_le B _ _).trans ?_
    refine gaussianConv_bound_aux ht hx B.opNorm_nonneg (abs_nonneg _) (norm_nonneg _) ?_
    have h := hC₁ (x - y)
    rw [norm_iteratedFDeriv_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun x y => B (g (x - y)) (f y))
    (F' := fun x y => B' (fderiv ℝ g (x - y)) (f y))
    (Metric.ball_mem_nhds x₀ one_pos)
    (Eventually.of_forall fun x =>
      gaussianConv_integrand_aesm B hgc hf.aestronglyMeasurable x)
    hint₀ hmeas' (ae_of_all _ fun y x hx => hle y x hx) hbound
    (ae_of_all _ fun y x _ => hasFDerivAt_gaussianConv_integrand hgd B f x y)

lemma gaussianConv_contDiff {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) (m : ℕ) :
    ∀ {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
      (B : F →L[ℝ] ℂ →L[ℝ] G) {g : EuclideanSpace ℝ (Fin n) → F},
      HasGaussianDerivBounds t g → ContDiff ℝ m (gaussianConv B g f) := by
  induction m with
  | zero =>
    intro F G _ _ _ _ _ B g hg
    have hcont : Continuous (gaussianConv B g f) := continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_gaussian_convolution ht hg hf B x).continuousAt
    have h0 : ContDiff ℝ 0 (gaussianConv B g f) := contDiff_zero.2 hcont
    simpa using h0
  | succ m ih =>
    intro F G _ _ _ _ _ B g hg
    have hd : Differentiable ℝ (gaussianConv B g f) := fun x =>
      (hasFDerivAt_gaussian_convolution ht hg hf B x).differentiableAt
    have heq : fderiv ℝ (gaussianConv B g f) =
        gaussianConv (gaussianConvDerivBilinear B) (fderiv ℝ g) f :=
      funext fun x => (hasFDerivAt_gaussian_convolution ht hg hf B x).fderiv
    have hnext := ih (gaussianConvDerivBilinear B) hg.fderiv
    rw [← heq] at hnext
    push_cast
    exact contDiff_succ_iff_fderiv.2 ⟨hd, by simp, hnext⟩

theorem heatConvN_contDiff {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (heatConvN n t f) := by
  have heq : heatConvN n t f =
      gaussianConv (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) (heatKernelN n t) f := by
    funext x
    simp only [heatConvN, gaussianConv, ContinuousLinearMap.lsmul_apply]
    rfl
  rw [heq]
  exact contDiff_infty.2 fun m =>
    gaussianConv_contDiff ht hf m _ (heatKernelN_hasGaussianDerivBounds ht)

/-- The heat kernel is continuous for `t > 0`. -/
lemma continuous_heatKernelN {t : ℝ} (ht : 0 < t) : Continuous (heatKernelN n t) := by
  unfold heatKernelN
  exact continuous_const.mul
    (Real.continuous_exp.comp ((continuous_norm.pow 2).neg.div_const _))

/-- Scaling the heat kernel: `G_s (√s • w) = s^(-n/2) • G_1 w`. -/
lemma heatKernelN_smul_sqrt {s : ℝ} (hs : 0 < s) (w : EuclideanSpace ℝ (Fin n)) :
    heatKernelN n s (Real.sqrt s • w) = s ^ (-(n : ℝ) / 2) * heatKernelN n 1 w := by
  have hsp : (0 : ℝ) < 4 * π * s := by positivity
  have h1p : (0 : ℝ) ≤ 4 * π := by positivity
  unfold heatKernelN
  have hnorm : ‖Real.sqrt s • w‖ ^ 2 = s * ‖w‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg s), mul_pow,
      Real.sq_sqrt hs.le]
  rw [hnorm]
  have hexp : -(s * ‖w‖ ^ 2) / (4 * s) = -‖w‖ ^ 2 / 4 := by
    field_simp
  rw [hexp, mul_one (4 * π), Real.mul_rpow h1p hs.le]
  ring

/-- Gaussian dilation: the `G_s`-weighted integral of a measurable `M` equals the
`G_1`-weighted integral of the dilated `M (√s • ·)`. -/
lemma lintegral_heatKernelN_mul_dilate {s : ℝ} (hs : 0 < s)
    {M : EuclideanSpace ℝ (Fin n) → ℝ≥0∞} (hM : Measurable M) :
    ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * M z ∂volume
      = ∫⁻ w, ENNReal.ofReal (heatKernelN n 1 w) * M (Real.sqrt s • w) ∂volume := by
  set c := Real.sqrt s with hc_def
  have hc : 0 < c := Real.sqrt_pos.2 hs
  have hφ : Measurable (fun z => ENNReal.ofReal (heatKernelN n s z) * M z) :=
    (ENNReal.measurable_ofReal.comp (continuous_heatKernelN hs).measurable).mul hM
  have hcn : c ^ n = s ^ ((n : ℝ) / 2) := by
    rw [hc_def, ← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hker : ∀ w : EuclideanSpace ℝ (Fin n),
      c ^ n * heatKernelN n s (c • w) = heatKernelN n 1 w := fun w => by
    have hks := heatKernelN_smul_sqrt hs w
    rw [← hc_def] at hks
    rw [hcn, hks, ← mul_assoc, ← Real.rpow_add hs,
      show (n : ℝ) / 2 + -(n : ℝ) / 2 = 0 from by ring, Real.rpow_zero, one_mul]
  have hmap : ∫⁻ w, ENNReal.ofReal (heatKernelN n s (c • w)) * M (c • w) ∂volume
      = ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * M z ∂(Measure.map (c • ·) volume) :=
    (lintegral_map hφ (continuous_const_smul c).measurable).symm
  rw [Measure.map_addHaar_smul volume hc.ne', finrank_euclideanSpace_fin,
    lintegral_smul_measure] at hmap
  have hcancel : ENNReal.ofReal (c ^ n) * ENNReal.ofReal |(c ^ n)⁻¹| = 1 := by
    rw [abs_of_nonneg (inv_nonneg.2 (pow_nonneg hc.le _)),
      ← ENNReal.ofReal_mul (pow_nonneg hc.le _), mul_inv_cancel₀ (pow_pos hc n).ne',
      ENNReal.ofReal_one]
  calc
    ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * M z ∂volume
        = ENNReal.ofReal (c ^ n) *
            ∫⁻ w, ENNReal.ofReal (heatKernelN n s (c • w)) * M (c • w) ∂volume := by
          rw [hmap, smul_eq_mul, ← mul_assoc, hcancel, one_mul]
    _ = ∫⁻ w, ENNReal.ofReal (c ^ n) *
          (ENNReal.ofReal (heatKernelN n s (c • w)) * M (c • w)) ∂volume := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ w, ENNReal.ofReal (heatKernelN n 1 w) * M (c • w) ∂volume := by
          apply lintegral_congr
          intro w
          rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hc.le _), hker w]

/-- Clause (c): `heatConvN n s f → f` in `L²` as `s → 0⁺`. -/
theorem heatConvN_eLpNorm_tendsto
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) :
    Tendsto (fun s => eLpNorm (fun x => heatConvN n s f x - f x) 2 volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- The squared translation error as a measurable function of the shift
  set M : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun z => ∫⁻ x, ‖hf.1.mk f (x - z) - hf.1.mk f x‖ₑ ^ 2 ∂volume with hM_def
  have hMmeas : Measurable M := by
    have hgm : Measurable (hf.1.mk f) := hf.1.measurable_mk
    have hψ : Measurable (Function.uncurry fun x z : EuclideanSpace ℝ (Fin n) =>
        ‖hf.1.mk f (x - z) - hf.1.mk f x‖ₑ ^ 2) := by
      have h1 : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          hf.1.mk f (p.1 - p.2)) := hgm.comp (measurable_fst.sub measurable_snd)
      have h2 : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
          hf.1.mk f p.1) := hgm.comp measurable_fst
      exact ((h1.sub h2).enorm).pow_const _
    exact hψ.lintegral_prod_left
  have hMeq : ∀ z, M z = (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 := fun z => by
    rw [hM_def, eLpNorm_translation_sub_sq z]
    apply lintegral_congr_ae
    have h1 : (fun x => f (x - z)) =ᶠ[ae (volume : Measure (EuclideanSpace ℝ (Fin n)))]
        fun x => hf.1.mk f (x - z) :=
      (measurePreserving_sub_right volume z).quasiMeasurePreserving.ae hf.1.ae_eq_mk
    have h2 : f =ᶠ[ae volume] hf.1.mk f := hf.1.ae_eq_mk
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1, hx2]
  have hMbound : ∀ z, M z ≤ (2 * eLpNorm f 2 volume) ^ 2 := fun z => by
    rw [hMeq z]
    exact pow_le_pow_left₀ (zero_le _) (eLpNorm_translation_sub_le_two hf z) 2
  have hC : (2 * eLpNorm f 2 volume : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hf.2.ne
  have hC2 : (2 * eLpNorm f 2 volume : ℝ≥0∞) ^ 2 ≠ ⊤ := by
    rw [pow_two]
    exact ENNReal.mul_ne_top hC hC
  -- The weighted average tends to zero, by dilation + dominated convergence
  have hlim : Tendsto
      (fun s => ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
        (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hmain : Tendsto
        (fun s => ∫⁻ w, ENNReal.ofReal (heatKernelN n 1 w) * M (Real.sqrt s • w) ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hbound_int : ∫⁻ w, ENNReal.ofReal (heatKernelN n 1 w) *
          (2 * eLpNorm f 2 volume) ^ 2 ∂volume ≠ ⊤ := by
        rw [lintegral_mul_const' _ _ hC2, heatKernelN_lintegral_eq_one one_pos,
          one_mul]
        exact hC2
      have hmeas : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
          Measurable (fun w => ENNReal.ofReal (heatKernelN n 1 w) * M (Real.sqrt s • w)) :=
        Eventually.of_forall fun s =>
          (ENNReal.measurable_ofReal.comp (continuous_heatKernelN one_pos).measurable).mul
            (hMmeas.comp (continuous_const_smul _).measurable)
      have hbound : ∀ᶠ s in nhdsWithin 0 (Set.Ioi 0),
          ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            ENNReal.ofReal (heatKernelN n 1 w) * M (Real.sqrt s • w)
              ≤ ENNReal.ofReal (heatKernelN n 1 w) * (2 * eLpNorm f 2 volume) ^ 2 :=
        Eventually.of_forall fun s => Eventually.of_forall fun w =>
          mul_le_mul_left' (hMbound _) _
      have hpt : ∀ᵐ w ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
          Tendsto (fun s => ENNReal.ofReal (heatKernelN n 1 w) * M (Real.sqrt s • w))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        Eventually.of_forall fun w => by
          have hsw : Tendsto (fun s : ℝ => Real.sqrt s • w)
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            have hcont : Continuous (fun s : ℝ => Real.sqrt s • w) :=
              Real.continuous_sqrt.smul continuous_const
            have h0 := hcont.tendsto 0
            rw [Real.sqrt_zero, zero_smul] at h0
            exact h0.mono_left nhdsWithin_le_nhds
          have hM0 : Tendsto M (nhds 0) (nhds 0) := by
            have hh0 := eLpNorm_translation_tendsto_eucl hf
            have hp := ENNReal.Tendsto.mul hh0 (Or.inr (by simp)) hh0 (Or.inr (by simp))
            rw [mul_zero] at hp
            have hfun : M = fun z => (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 :=
              funext hMeq
            rw [hfun]
            exact hp.congr' (Eventually.of_forall fun z => (pow_two _).symm)
          have h3 := hM0.comp hsw
          have h4 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (heatKernelN n 1 w))
            h3 (Or.inr ENNReal.ofReal_ne_top)
          rw [mul_zero] at h4
          exact h4.congr' (Eventually.of_forall fun s => rfl)
      have hdct := tendsto_lintegral_filter_of_dominated_convergence
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (l := nhdsWithin 0 (Set.Ioi 0))
        (bound := fun w => ENNReal.ofReal (heatKernelN n 1 w) * (2 * eLpNorm f 2 volume) ^ 2)
        (F := fun s w => ENNReal.ofReal (heatKernelN n 1 w) * M (Real.sqrt s • w))
        (f := fun _ => (0 : ℝ≥0∞))
        hmeas hbound hbound_int hpt
      simpa using hdct
    have hcong :
        (fun s => ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
          (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume)
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun s => ∫⁻ w, ENNReal.ofReal (heatKernelN n 1 w) * M (Real.sqrt s • w) ∂volume := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      have heq : ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
            (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume
          = ∫⁻ z, ENNReal.ofReal (heatKernelN n s z) * M z ∂volume := by
        apply lintegral_congr
        intro z
        rw [← hMeq z]
      rw [heq, lintegral_heatKernelN_mul_dilate hs hMmeas]
    exact hmain.congr' hcong.symm
  -- squeeze
  have hrpow : Tendsto
      (fun s => (∫⁻ z, ENNReal.ofReal (heatKernelN n s z) *
        (eLpNorm (fun x => f (x - z) - f x) 2 volume) ^ 2 ∂volume) ^ (1 / 2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hcont := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0
    have hcomp := hcont.comp hlim
    rwa [ENNReal.zero_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at hcomp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrpow
    (Eventually.of_forall fun s => zero_le _)
    (by filter_upwards [self_mem_nhdsWithin] with s hs
        exact eLpNorm_heatConvN_sub_le hs hf)

/-- **Reformed a96A04** (see PRELIM-DEFECT.md): the heat kernel on `ℝⁿ = EuclideanSpace
ℝ (Fin n)`, complex-valued `f ∈ L²` (Lebesgue measurable), `t > 0`:

(a) `u(·,t)` is smooth in `x`;
(b) `‖u(·,t)‖₂ ≤ ‖f‖₂`;
(c) `u(·,t) → f` in `L²` as `t → 0⁺`. -/
theorem apm_a96a04 {n : ℕ} {t : ℝ} (ht : 0 < t)
    {f : EuclideanSpace ℝ (Fin n) → ℂ} (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (heatConvN n t f) ∧
    eLpNorm (heatConvN n t f) 2 volume ≤ eLpNorm f 2 volume ∧
    Tendsto (fun s => eLpNorm (fun x => heatConvN n s f x - f x) 2 volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  ⟨heatConvN_contDiff ht hf, heatConvN_eLpNorm_le ht hf, heatConvN_eLpNorm_tendsto hf⟩

end Main
