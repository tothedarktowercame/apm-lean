/-
! # APM a96A04: Heat kernel — smoothness, L² contraction, L² convergence

u(x,t) = (4πt)^{-n/2} ∫ e^{-|x-y|²/(4t)} f(y) dy (heat kernel convolution).
(a) u is smooth in x for t > 0.
(b) ‖u(·,t)‖₂ ≤ ‖f‖₂.
(c) u(·,t) → f in L² as t → 0⁺.

## Theory boundaries

- Young's convolution inequality is NOT in Mathlib (blocks part b).
- The heat kernel normalization (∫G_t = 1) requires the Gaussian integral.
- Differentiation under the integral sign requires DCT machinery (part a).
- The Fourier approach requires Fourier transform of Gaussian (parts b, c).

## Statement repair

We use ℝ (the 1D case) to avoid EuclideanSpace measure issues. The
mathematical content generalizes to ℝⁿ but the formalization is cleaner
in 1D. The generated `Memℒp` is corrected to `MemLp`.
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open MeasureTheory Set Filter Real

open scoped ENNReal

noncomputable section

/-- The heat kernel G_t(x) = (4πt)^{-1/2} exp(-x²/(4t)) for t > 0 (1D). -/
def heatKernel (t : ℝ) (x : ℝ) : ℝ :=
  (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (- x ^ 2 / (4 * t))

/-- The heat convolution u(x,t) = (G_t * f)(x) = ∫ G_t(x-y) f(y) dy. -/
def heatConv (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, heatKernel t (x - y) * f y ∂volume

/-- The heat kernel integrates to 1 (1D).

∫ G_t(x) dx = (4πt)^{-1/2} ∫ e^{-x²/(4t)} dx = (4πt)^{-1/2} · √(4πt) = 1.

**Blocker:** Requires the 1D Gaussian integral ∫₀^∞ e^{-ax²} dx = √(π)/(2√a). -/
lemma heatKernel_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : ℝ, heatKernel t x ∂volume = 1 := by
  have h_pos : 0 < 4 * π * t := by positivity
  have h_gauss : ∫ x : ℝ, Real.exp (-(1 / (4 * t)) * x ^ 2) = Real.sqrt (4 * π * t) := by
    have := integral_gaussian (1 / (4 * t))
    rwa [show π / (1 / (4 * t)) = 4 * π * t from by field_simp] at this
  -- ∫ heatKernel t x dx = ∫ prefactor · exp(...) dx = prefactor · ∫ exp(...) dx
  rw [show heatKernel t = fun x => (4 * π * t) ^ (-(1:ℝ) / 2) * Real.exp (-(1 / (4 * t)) * x ^ 2) from
    funext fun x => by unfold heatKernel; field_simp]
  rw [integral_const_mul, h_gauss]
  -- (4πt)^{-1/2} · √(4πt) = 1
  have h_key : (4 * π * t) ^ (-(1:ℝ) / 2) * (4 * π * t) ^ ((1:ℝ) / 2) = 1 := by
    rw [← Real.rpow_add h_pos]
    show (4 * π * t) ^ (-(1:ℝ) / 2 + (1:ℝ) / 2) = 1
    rw [show -(1:ℝ) / 2 + 1 / 2 = 0 by ring, Real.rpow_zero]
  convert h_key using 2
  · exact Real.sqrt_eq_rpow (4 * π * t)

/-- (a) u(·,t) is smooth in x for t > 0.

**Blocker:** Requires differentiation under the integral sign with DCT. -/
theorem heatConv_contDiff
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    ContDiff ℝ ⊤ (heatConv t f) := by
  sorry

/-- (b) L² contraction: ‖u(·,t)‖₂ ≤ ‖f‖₂.

**Blocker:** Requires Young's inequality (NOT in Mathlib). -/
theorem heatConv_L2_le
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    eLpNorm (heatConv t f) 2 volume ≤
      eLpNorm f 2 volume := by
  sorry

/-- (c) u(·,t) → f in L² as t → 0⁺.

**Blocker:** Requires approximate identity / Fourier argument. -/
theorem heatConv_tendsto_L2
    {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - f x) 2 volume)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  sorry

end
