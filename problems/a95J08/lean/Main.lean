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
  sorry

/-- (a) The integrand f(x-·)g(·) is in L¹ for a.e. x.

**Blocker:** Requires the Hölder + Tonelli argument:
∫|f(x-y)||g(y)|^p dy < ∞ a.e. via Tonelli on the product, then
Hölder to bound ∫|f(x-y)g(y)| dy. Needs product measure setup. -/
theorem convolution_integrand_integrableAE
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 < p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    ∀ᵐ x ∂volume,
      Integrable (fun y => f (x - y) * g y) volume := by
  sorry

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

/-- The convolution is in Lp. -/
theorem convolution_memLp
    {f g : ℝ → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hf : Integrable f volume)
    (hg : MemLp g p volume) :
    MemLp (convolution f g) p volume := by
  sorry

end
