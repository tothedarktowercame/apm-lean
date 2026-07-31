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

/-- (b) Young's inequality: ‖f * g‖_p ≤ ‖f‖₁ · ‖g‖_p.

The endpoint `p = 1` is discharged above by Tonelli and Haar translation
invariance.  For `1 < p < ∞`, the remaining construction is the weighted
Hölder/Jensen estimate

`(∫ w * v) ^ p ≤ (∫ w) ^ (p - 1) * ∫ w * v ^ p`.

Mathlib has scalar Hölder and finite-sum/function Minkowski inequalities, but
not this parameter-integral form or Young's convolution inequality itself.
After that estimate, the same Tonelli calculation as in the endpoint proof
finishes the theorem. -/
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
  · sorry

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
