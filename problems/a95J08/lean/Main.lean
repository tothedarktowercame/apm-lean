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

/-- (b) Young's inequality: ‖f * g‖_p ≤ ‖f‖₁ · ‖g‖_p.

**Blocker:** Young's convolution inequality is NOT in Mathlib.
The proof requires Minkowski's integral inequality or the
Hölder + Tonelli + Fubini chain described in the informal proof. -/
theorem young_convolution_inequality
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    eLpNorm (convolution f g) p volume ≤
      eLpNorm f 1 volume * eLpNorm g p volume := by
  sorry

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
