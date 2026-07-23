

# APM a96A04: Heat kernel — smoothness, L² contraction, L² convergence to initial data

## 1. Informal proof

**Why it's hard.** The heat kernel Gₜ(x) = (4πt)^{-n/2} e^{-|x|²/(4t)} is smooth in x and t but its convolution with f ∈ L² requires careful justification: (a) smoothness of u in x means differentiating under the integral sign infinitely often, (b) the L² bound requires Young's inequality or Fourier analysis, and (c) L² convergence as t → 0⁺ is an approximate identity result on an infinite measure space.

**The key insight.** Everything is cleanest via the Fourier transform: Ĝₜ(ξ) = e^{-4π²|ξ|²t}, so û = Ĝₜ · f̂. (a) Smoothness: x-derivatives of Gₜ multiply f̂ by polynomials in ξ times the Gaussian — always in L². (b) L² bound: |Ĝₜ| ≤ 1, so ||û||₂ = ||Ĝₜ f̂||₂ ≤ ||f̂||₂ = ||f||₂ by Plancherel. (c) Convergence: Ĝₜ → 1 pointwise as t → 0⁺, and |Ĝₜ f̂| ≤ |f̂| ∈ L², so DCT gives ||û - f̂||₂ → 0.

**Proof.**

u(x,t) = (Gₜ * f)(x) where Gₜ(x) = (4πt)^{-n/2} exp(-|x|²/(4t)).

**(a) u is smooth in x (for fixed t > 0).**

Differentiate under the integral: ∂ₓᵅ u(x,t) = ∫ (∂ₓᵅ Gₜ)(x-y) f(y) dy. The derivative ∂ₓᵅ Gₜ(x) is Gₜ(x) times a polynomial in x/√t (Hermite-type), hence still in L¹ ∩ L² for each fixed t > 0. The dominated convergence theorem justifies the interchange (the difference quotient is dominated by a Schwartz function times |f|). Since α is arbitrary, u is C^∞ in x. ✓

**(b) ||u(·,t)||₂ ≤ ||f||₂.**

Method 1 (Fourier): The Fourier transform of Gₜ is Ĝₜ(ξ) = e^{-4π²|ξ|²t}. By the convolution theorem: û(ξ,t) = Ĝₜ(ξ) · f̂(ξ). Since |Ĝₜ(ξ)| = e^{-4π²|ξ|²t} ≤ 1:

||u(·,t)||₂ = ||û(·,t)||₂ = ||Ĝₜ · f̂||₂ ≤ ||f̂||₂ = ||f||₂ (Plancherel). ✓

Method 2 (Young): Gₜ ∈ L¹ with ||Gₜ||₁ = 1. Young's inequality: ||Gₜ * f||₂ ≤ ||Gₜ||₁ · ||f||₂ = ||f||₂. ✓

**(c) u(·,t) → f in L² as t → 0⁺.**

||u(·,t) - f||₂² = ||Ĝₜ f̂ - f̂||₂² = ∫ |e^{-4π²|ξ|²t} - 1|² |f̂(ξ)|² dξ.

The integrand converges to 0 pointwise (e^{-4π²|ξ|²t} → 1 for each ξ) and is bounded by 4|f̂(ξ)|² ∈ L¹ (since |e^{-s}-1| ≤ 2). By DCT: ∫ → 0, so ||u(·,t)-f||₂ → 0. ✓ ∎

**What connects.** u(x,t) is the solution to the heat equation ∂ₜu = Δu with initial data u(·,0) = f. The three parts verify the well-posedness: (a) the solution is smooth for t > 0 (instantaneous regularisation — a hallmark of parabolic equations), (b) the L² norm doesn't increase (energy dissipation — the heat equation is contractive), (c) the solution recovers the initial data in L² as t → 0⁺ (continuity at the initial time). The Fourier-analytic proof is the cleanest because the heat kernel diagonalises in Fourier space: Ĝₜ = e^{-4π²|ξ|²t} acts as a multiplier, making all estimates transparent. This is the prototypical approximate identity in ℝⁿ.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic

open MeasureTheory Set Filter Real

noncomputable section

variable {n : ℕ}

/-- The heat kernel G_t(x) = (4πt)^{-n/2} exp(-|x|²/(4t)). -/
def heatKernel (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  (4 * π * t) ^ (-(n : ℝ) / 2) * exp (-‖x‖ ^ 2 / (4 * t))

/-- The heat convolution u(x,t) = G_t * f. -/
def heatConv (t : ℝ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, heatKernel t (x - y) * f y ∂volume

/-- The heat kernel integrates to 1. -/
lemma heatKernel_integral {t : ℝ} (ht : 0 < t) :
    ∫ x : Fin n → ℝ, heatKernel t x ∂volume = 1 := by
  sorry

/-- (a) u(·,t) is smooth in x for t > 0. -/
theorem heatConv_contDiff
    {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ}
    (hf : Memℒp f 2 volume) :
    ContDiff ℝ ⊤ (heatConv t f) := by
  sorry

/-- (b) L² contraction: ‖u(·,t)‖₂ ≤ ‖f‖₂. -/
theorem heatConv_L2_le
    {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ}
    (hf : Memℒp f 2 volume) :
    eLpNorm (heatConv t f) 2 volume ≤
      eLpNorm f 2 volume := by
  sorry

/-- (c) u(·,t) → f in L² as t → 0⁺. -/
theorem heatConv_tendsto_L2
    {f : (Fin n → ℝ) → ℝ}
    (hf : Memℒp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    Tendsto (fun t => eLpNorm (fun x => heatConv t f x - f x) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Differentiation under the integral sign for the heat convolution. -/
lemma heatConv_hasFDerivAt
    {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ}
    (hf : Memℒp f 2 volume)
    (x : Fin n → ℝ) :
    HasFDerivAt (heatConv t f)
      (∫ y, fderiv ℝ (fun x' => heatKernel t (x' - y)) x • f y ∂volume) x := by
  sorry

/-- Young's inequality: ‖G_t * f‖₂ ≤ ‖G_t‖₁ · ‖f‖₂ = ‖f‖₂. -/
lemma young_heat_L2
    {t : ℝ} (ht : 0 < t)
    {f : (Fin n → ℝ) → ℝ}
    (hf : Memℒp f 2 volume) :
    eLpNorm (heatConv t f) 2 volume ≤
      eLpNorm (heatKernel t) 1 volume * eLpNorm f 2 volume := by
  sorry

/-- The Fourier multiplier of the heat kernel: Ĝ_t(ξ) = e^{-4π²|ξ|²t}. -/
lemma heatKernel_fourier_transform {t : ℝ} (ht : 0 < t) (ξ : Fin n → ℝ) :
    True := by -- placeholder for Ĝ_t(ξ) = e^{-4π²‖ξ‖²t}
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Memℒp f 2 volume` — f ∈ L²(ℝⁿ)
- `MeasureTheory.eLpNorm` — Lp seminorm
- `ContDiff ℝ ⊤ f` — infinitely smooth (C^∞)
- `HasFDerivAt` — Fréchet differentiability
- `Fin n → ℝ` — ℝⁿ with `volume` as Lebesgue measure
- `Filter.𝓝[>] 0` — right-neighbourhood filter

**Key lemmas:**
- `integral_gaussian` — ∫ e^{-bx²} = √(π/b). For verifying ∫G_t = 1. In `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- Young's inequality — `MeasureTheory.convolution_le_Lp_mul_L1` or similar. For part (b)
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — DCT. For the Fourier-space argument in part (c) and for differentiation under the integral in part (a)
- `ContDiff.integral_clm` — differentiating under the integral sign for parameter-dependent integrals. For part (a)
- `hasDerivAt_integral_of_dominated_convergence` — differentiation under integral. In `Mathlib.MeasureTheory.Integral.DominatedConvergence`
- `Real.exp_neg_mul_sq_le` — Gaussian tail bounds
- `MeasureTheory.Lp.tendsto_approx` — density for approximation arguments

**Tactic hints:**
- `apply ContDiff.integral_clm` — for part (a), differentiating under ∫
- `exact young_heat_L2 ht hf |>.trans (by simp [heatKernel_integral ht])` — for part (b)
- `apply tendsto_integral_of_dominated_convergence (fun x => 4 * ‖f̂ x‖^2)` — DCT in Fourier for part (c)
- `simp [heatKernel, Real.exp_neg]` — unfolding definitions
- `positivity` — for t > 0, 4πt > 0
- `gcongr` — for ‖Ĝₜ · f̂‖ ≤ ‖f̂‖
- `field_simp` — for (4πt)^{-n/2} arithmetic
- `exact?` — finding the Gaussian integral or Young's inequality