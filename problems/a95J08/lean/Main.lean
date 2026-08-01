/-
! # APM a95J08: Young's convolution inequality — f ∈ L¹, g ∈ Lp implies f*g ∈ Lp

(a) For a.e. x, y ↦ f(x-y)g(y) is in L¹.
(b) ‖f*g‖_p ≤ ‖f‖₁ · ‖g‖_p (Young's inequality, case (1,p,p)).

## Theory boundaries

- Young's convolution inequality is NOT in Mathlib (established in a95A03).
- Hölder's inequality IS in Mathlib (`MeasureTheory.integral_mul_le_eLpNorm`).
- Translation invariance IS available via `volume.measurePreserving_sub_left`.
- The Tonelli/Fubini step requires product measure setup.

## Statement repair

The generated `convolution` uses Bochner integral directly, which is correct.
We keep this. The `MemLp` type is used (Mathlib's name, not `Memℒp`).
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.Convolution

open MeasureTheory Set Filter

open scoped ENNReal

noncomputable section

/-- The convolution h = f * g at point x: ∫ f(x-y)g(y) dy. -/
def convolution (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, f (x - y) * g y ∂volume

/-- Translation invariance: ∫|f(x-y)| dx = ∫|f(x)| dx for all y.

This follows from `volume.measurePreserving_sub_left`. -/
lemma integral_translate_norm
    {f : ℝ → ℝ} (hf : Integrable f volume) (y : ℝ) :
    ∫ x, ‖f (x - y)‖ ∂volume = ∫ x, ‖f x‖ ∂volume := by
  exact integral_sub_right_eq_self (μ := volume) (fun x : ℝ ↦ ‖f x‖) y

/-- (a) The integrand f(x-·)g(·) is in L¹ for a.e. x.

Split `g` into its bounded part on `{‖g‖ ≤ 1}` and its integrable part on
`{1 < ‖g‖}`. The first product is dominated pointwise by a translate of `‖f‖`;
the second follows from Fubini for the convolution of two integrable functions. -/
theorem convolution_integrand_integrableAE
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    ∀ᵐ x ∂volume,
      Integrable (fun y => f (x - y) * g y) volume := by
  let s : Set ℝ := {y | 1 < ‖g y‖}
  have hs : NullMeasurableSet s volume :=
    aestronglyMeasurable_const.nullMeasurableSet_lt hg.1.norm
  have hp0 : p ≠ 0 := ne_of_gt (lt_trans zero_lt_one hp)
  have hp_real : 1 ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp' hp.le
  have hlarge_meas : AEStronglyMeasurable (s.indicator g) volume :=
    hg.1.indicator₀ hs
  have hlarge : Integrable (s.indicator g) volume := by
    refine (hg.integrable_norm_rpow hp0 hp').mono' hlarge_meas ?_
    filter_upwards with y
    by_cases hy : y ∈ s
    · simpa [hy] using Real.self_le_rpow_of_one_le (le_of_lt hy) hp_real
    · simp [hy]
      positivity
  have hsmall_meas : AEStronglyMeasurable (sᶜ.indicator g) volume :=
    hg.1.indicator₀ hs.compl
  have hsmall : ∀ x : ℝ, Integrable (fun y => f (x - y) * sᶜ.indicator g y) volume := by
    intro x
    refine (hf.comp_sub_left x).norm.mono'
      ((hf.comp_sub_left x).aestronglyMeasurable.mul hsmall_meas) ?_
    filter_upwards with y
    by_cases hy : y ∈ s
    · simp [hy]
    · have hyg : ‖g y‖ ≤ 1 := not_lt.mp hy
      have hind : sᶜ.indicator g y = g y := by simp [Set.indicator, hy]
      rw [norm_mul, hind]
      exact mul_le_of_le_one_right (norm_nonneg _) hyg
  have hlarge_ae :
      ∀ᵐ x ∂volume, Integrable (fun y => s.indicator g y * f (x - y)) volume :=
    hlarge.ae_convolution_exists (L := ContinuousLinearMap.mul ℝ ℝ) hf
  filter_upwards [hlarge_ae] with x hx
  have hx' : Integrable (fun y => f (x - y) * s.indicator g y) volume :=
    hx.congr (Eventually.of_forall fun y => mul_comm _ _)
  refine (hx'.add (hsmall x)).congr (Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ s <;> simp [hy]

/-- The convolution has a strongly measurable representative whenever both inputs do. -/
lemma convolution_aestronglyMeasurable
    {f g : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hg : AEStronglyMeasurable g volume) :
    AEStronglyMeasurable (convolution f g) volume := by
  have hprod :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => g p.2 * f (p.1 - p.2)) (volume.prod volume) :=
    hg.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hf
  have hprod' :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ => f (p.1 - p.2) * g p.2) (volume.prod volume) :=
    hprod.congr (Eventually.of_forall fun p => mul_comm _ _)
  exact hprod'.integral_prod_right'

/-- Young's convolution inequality at the endpoint `p = 1`.

This isolates the Tonelli and translation-invariance half of the general
argument.  The remaining finite-exponent case additionally needs the weighted
Hölder/Jensen estimate described below. -/
lemma young_convolution_inequality_one
    {f g : ℝ → ℝ}
    (hf : Integrable f volume)
    (hg : MemLp g 1 volume) :
    eLpNorm (_root_.convolution f g) 1 volume ≤
      eLpNorm f 1 volume * eLpNorm g 1 volume := by
  have hg_int : Integrable g volume := memLp_one_iff_integrable.mp hg
  have h_joint :
      AEMeasurable
        (Function.uncurry fun x y : ℝ => ‖f (x - y)‖ₑ * ‖g y‖ₑ)
        (volume.prod volume) := by
    have hf_joint : AEMeasurable
        (fun z : ℝ × ℝ => ‖f (z.1 - z.2)‖ₑ)
        (volume.prod volume) := by
      simpa [Function.comp_def] using
        (hf.aestronglyMeasurable.enorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub (volume : Measure ℝ) volume))
    exact hf_joint.mul hg.aestronglyMeasurable.enorm.comp_snd
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm]
  calc
    (∫⁻ x, ‖_root_.convolution f g x‖ₑ ∂volume)
        ≤ ∫⁻ x, (∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂volume) ∂volume := by
          apply lintegral_mono
          intro x
          exact (enorm_integral_le_lintegral_enorm _).trans_eq <| by
            apply lintegral_congr
            intro y
            simp
    _ = ∫⁻ y, (∫⁻ x, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂volume) ∂volume := by
          rw [lintegral_lintegral_swap h_joint]
    _ = (∫⁻ x, ‖f x‖ₑ ∂volume) * (∫⁻ y, ‖g y‖ₑ ∂volume) := by
          calc
            (∫⁻ y, (∫⁻ x, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂volume) ∂volume)
                = ∫⁻ y, (∫⁻ x, ‖f (x - y)‖ₑ ∂volume) * ‖g y‖ₑ ∂volume := by
                    apply lintegral_congr
                    intro y
                    rw [lintegral_mul_const' _ _ (by finiteness)]
            _ = ∫⁻ y, (∫⁻ x, ‖f x‖ₑ ∂volume) * ‖g y‖ₑ ∂volume := by
                    apply lintegral_congr
                    intro y
                    congr 1
                    simpa [sub_eq_add_neg] using
                      lintegral_add_right_eq_self (μ := volume)
                        (fun x => ‖f x‖ₑ) (-y)
            _ = (∫⁻ x, ‖f x‖ₑ ∂volume) * (∫⁻ y, ‖g y‖ₑ ∂volume) := by
                    rw [lintegral_const_mul' _ _ (by
                      exact ne_of_lt hf.hasFiniteIntegral)]

/-- Weighted Hölder in the form needed for Young's convolution inequality.

This formulation is total in `ℝ≥0∞`; the zero and infinity cases are handled
by `ENNReal.lintegral_mul_norm_pow_le`. -/
lemma lintegral_mul_le_lintegral_rpow
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {w v : α → ℝ≥0∞} (hw : AEMeasurable w μ) (hv : AEMeasurable v μ)
    {r : ℝ} (hr : 1 < r) :
    (∫⁻ x, w x * v x ∂μ) ≤
      (∫⁻ x, w x ∂μ) ^ (1 - 1 / r) *
        (∫⁻ x, w x * v x ^ r ∂μ) ^ (1 / r) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have ha : 0 ≤ 1 - 1 / r := by
    rw [sub_nonneg, div_le_one hr0]
    exact hr.le
  have hb : 0 ≤ 1 / r := by positivity
  have hab : (1 - 1 / r) + 1 / r = 1 := by ring
  have hri : r * (1 / r) = 1 := by field_simp
  have h := ENNReal.lintegral_mul_norm_pow_le hw
    (hw.mul (hv.pow_const r)) ha hb hab
  convert h using 1
  apply lintegral_congr
  intro x
  · rw [ENNReal.mul_rpow_of_nonneg _ _ hb,
      ← mul_assoc,
      ← ENNReal.rpow_add_of_nonneg _ _ ha hb,
      hab, ENNReal.rpow_one, ← ENNReal.rpow_mul, hri,
      ENNReal.rpow_one]

/-- (b) Young's inequality: ‖f * g‖_p ≤ ‖f‖₁ · ‖g‖_p.

The endpoint `p = 1` is discharged above by Tonelli and Haar translation
invariance.  For `1 < p < ∞`, the proof uses the weighted Hölder estimate

`(∫ w * v) ^ p ≤ (∫ w) ^ (p - 1) * ∫ w * v ^ p`.

packaged above from `ENNReal.lintegral_mul_norm_pow_le`; Tonelli and Haar
translation invariance then finish the estimate. -/
theorem young_convolution_inequality
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    eLpNorm (convolution f g) p volume ≤
      eLpNorm f 1 volume * eLpNorm g p volume := by
  by_cases hpeq : p = 1
  · subst p
    exact young_convolution_inequality_one hf hg
  · have hpgt : 1 < p := lt_of_le_of_ne hp (Ne.symm hpeq)
    have hp0 : p ≠ 0 := ne_of_gt (zero_lt_one.trans hpgt)
    let r := p.toReal
    have hr : 1 < r := by
      exact ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp' |>.2 (by simpa [r] using hpgt)
    have hr0 : 0 < r := zero_lt_one.trans hr
    have ha : 0 ≤ 1 - 1 / r := by
      rw [sub_nonneg, div_le_one hr0]
      exact hr.le
    have hb : 0 ≤ 1 / r := by positivity
    have hri : r * (1 / r) = 1 := by field_simp
    have hir : (1 / r) * r = 1 := by field_simp
    have har : (1 - 1 / r) * r = r - 1 := by field_simp
    let A := ∫⁻ x, ‖f x‖ₑ ∂volume
    let G := ∫⁻ y, ‖g y‖ₑ ^ r ∂volume
    let H := fun x : ℝ => ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ^ r ∂volume
    have hpoint : ∀ x, ‖convolution f g x‖ₑ ≤ A ^ (1 - 1 / r) * H x ^ (1 / r) := by
      intro x
      calc
        ‖convolution f g x‖ₑ ≤ ∫⁻ y, ‖f (x - y) * g y‖ₑ ∂volume :=
          enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ y, ‖f (x - y)‖ₑ * ‖g y‖ₑ ∂volume := by simp only [enorm_mul]
        _ ≤ (∫⁻ y, ‖f (x - y)‖ₑ ∂volume) ^ (1 - 1 / r) *
              H x ^ (1 / r) := by
          exact lintegral_mul_le_lintegral_rpow
            (hf.comp_sub_left x).1.enorm hg.1.enorm hr
        _ = A ^ (1 - 1 / r) * H x ^ (1 / r) := by
          congr 2
          simpa [A] using
            (volume.measurePreserving_sub_left x).lintegral_comp_emb
              (measurableEmbedding_subLeft x) (fun z => ‖f z‖ₑ)
    have hf_joint : AEMeasurable
        (fun z : ℝ × ℝ => ‖f (z.1 - z.2)‖ₑ) (volume.prod volume) := by
      simpa [Function.comp_def] using
        (hf.1.enorm.comp_quasiMeasurePreserving
          (quasiMeasurePreserving_sub (volume : Measure ℝ) volume))
    have h_joint : AEMeasurable
        (Function.uncurry fun x y : ℝ => ‖f (x - y)‖ₑ * ‖g y‖ₑ ^ r)
        (volume.prod volume) :=
      hf_joint.mul ((hg.1.enorm.pow_const r).comp_snd)
    have hH : (∫⁻ x, H x ∂volume) = A * G := by
      rw [lintegral_lintegral_swap h_joint]
      simp only [A, G]
      calc
        (∫⁻ y, ∫⁻ x, ‖f (x - y)‖ₑ * ‖g y‖ₑ ^ r ∂volume ∂volume)
            = ∫⁻ y, (∫⁻ x, ‖f (x - y)‖ₑ ∂volume) * ‖g y‖ₑ ^ r ∂volume := by
                apply lintegral_congr
                intro y
                rw [lintegral_mul_const' _ _ (by finiteness)]
        _ = ∫⁻ y, A * ‖g y‖ₑ ^ r ∂volume := by
                apply lintegral_congr
                intro y
                congr 1
                simpa [A, sub_eq_add_neg] using
                  lintegral_add_right_eq_self (μ := volume) (fun z => ‖f z‖ₑ) (-y)
        _ = A * G := by
                rw [lintegral_const_mul' _ _ (by
                  exact ne_of_lt hf.hasFiniteIntegral)]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp', eLpNorm_one_eq_lintegral_enorm,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp']
    change (∫⁻ x, ‖_root_.convolution f g x‖ₑ ^ r ∂volume) ^ (1 / r) ≤
      A * (∫⁻ y, ‖g y‖ₑ ^ r ∂volume) ^ (1 / r)
    calc
      (∫⁻ x, ‖_root_.convolution f g x‖ₑ ^ r ∂volume) ^ (1 / r)
          ≤ (∫⁻ x, (A ^ (1 - 1 / r) * H x ^ (1 / r)) ^ r ∂volume) ^
              (1 / r) := by
            apply ENNReal.rpow_le_rpow _ hb
            apply lintegral_mono
            intro x
            exact ENNReal.rpow_le_rpow (hpoint x) hr0.le
      _ = (A ^ (r - 1) * (∫⁻ x, H x ∂volume)) ^ (1 / r) := by
            congr 1
            calc
              (∫⁻ x, (A ^ (1 - 1 / r) * H x ^ (1 / r)) ^ r ∂volume)
                  = ∫⁻ x, A ^ (r - 1) * H x ∂volume := by
                      apply lintegral_congr
                      intro x
                      rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le,
                        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, har, hir,
                        ENNReal.rpow_one]
              _ = A ^ (r - 1) * (∫⁻ x, H x ∂volume) := by
                      rw [lintegral_const_mul' _ _ (by
                        exact ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hr.le)
                          (ne_of_lt hf.hasFiniteIntegral))]
      _ = (A ^ r * G) ^ (1 / r) := by
            rw [hH, ← mul_assoc]
            congr 1
            apply congrArg (fun z : ℝ≥0∞ => z * G)
            calc
              A ^ (r - 1) * A = A ^ (r - 1) * A ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
              _ = A ^ ((r - 1) + 1) :=
                (ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hr.le) zero_le_one).symm
              _ = A ^ r := by ring_nf
      _ = A * G ^ (1 / r) := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ hb, ← ENNReal.rpow_mul, hri,
              ENNReal.rpow_one]

/-- The convolution is in Lp.

Once the sharp Young estimate is available, strong measurability is supplied
by `convolution_aestronglyMeasurable`, while finiteness follows because the
product of the finite `L¹` and `Lᵖ` seminorms is finite. -/
theorem convolution_memLp
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    MemLp (convolution f g) p volume := by
  refine ⟨convolution_aestronglyMeasurable hf.1 hg.1, ?_⟩
  refine (young_convolution_inequality hp hp' hf hg).trans_lt ?_
  exact ENNReal.mul_lt_top
    (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
    hg.eLpNorm_lt_top

end
