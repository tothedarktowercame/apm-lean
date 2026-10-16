

# APM a96A04: Heat kernel — smoothness, $L^{2}$ contraction, $L^{2}$ convergence to initial data

## 1. Informal proof

**Why it's hard.** The heat kernel $G_{t}(x) = (4\pi t)^{-n/2} e^{-|x|^{2}/(4t)}$ is smooth in $x$ and $t$ but its convolution with $f \in L^{2}$ requires careful justification: (a) smoothness of $u$ in $x$ means differentiating under the integral sign infinitely often, (b) the $L^{2}$ bound requires Young's inequality or Fourier analysis, and (c) $L^{2}$ convergence as $t \to 0^{+}$ is an approximate identity result on an infinite measure space.

**The key insight.** Everything is cleanest via the Fourier transform: $\hat{G}_{t}(\xi) = e^{-4\pi^{2}|\xi|^{2}t}$, so $\hat{u} = \hat{G}_{t} \cdot \hat{f}$. (a) Smoothness: $x$-derivatives of $G_{t}$ multiply $\hat{f}$ by polynomials in $\xi$ times the Gaussian — always in $L^{2}$. (b) $L^{2}$ bound: $|\hat{G}_{t}| \leq 1$, so $||\hat{u}||_{2} = ||\hat{G}_{t} \hat{f}||_{2} \leq ||\hat{f}||_{2} = ||f||_{2}$ by Plancherel. (c) Convergence: $\hat{G}_{t} \to 1$ pointwise as $t \to 0^{+}$, and $|\hat{G}_{t} \hat{f}| \leq |\hat{f}| \in L^{2}$, so DCT gives $||\hat{u} - \hat{f}||_{2} \to 0$.

**Proof.**

$u(x,t) = (G_{t} * f)(x)$ where $G_{t}(x) = (4\pi t)^{-n/2} \exp(-|x|^{2}/(4t))$.

**(a) $u$ is smooth in $x$ (for fixed $t > 0$).**

Differentiate under the integral: $\partial_{x}^{\alpha} u(x,t) = \int (\partial_{x}^{\alpha} G_{t})(x-y) f(y) dy$. The derivative $\partial_{x}^{\alpha} G_{t}(x)$ is $G_{t}(x)$ times a polynomial in $x/\sqrt{t}$ (Hermite-type), hence still in $L^{1} \cap L^{2}$ for each fixed $t > 0$. The dominated convergence theorem justifies the interchange (the difference quotient is dominated by a Schwartz function times $|f|$). Since $\alpha$ is arbitrary, $u$ is $C^\infty$ in $x$. ✓

**(b) $||u(\cdot,t)||_{2} \leq ||f||_{2}$.**

Method 1 (Fourier): The Fourier transform of $G_{t}$ is $\hat{G}_{t}(\xi) = e^{-4\pi^{2}|\xi|^{2}t}$. By the convolution theorem: $\hat{u}(\xi,t) = \hat{G}_{t}(\xi) \cdot \hat{f}(\xi)$. Since $|\hat{G}_{t}(\xi)| = e^{-4\pi^{2}|\xi|^{2}t} \leq 1$:

$||u(\cdot,t)||_{2} = ||\hat{u}(\cdot,t)||_{2} = ||\hat{G}_{t} \cdot \hat{f}||_{2} \leq ||\hat{f}||_{2} = ||f||_{2}$ (Plancherel). ✓

Method 2 (Young): $G_{t} \in L^{1}$ with $||G_{t}||_{1} = 1$. Young's inequality: $||G_{t} * f||_{2} \leq ||G_{t}||_{1} \cdot ||f||_{2} = ||f||_{2}$. ✓

**(c) $u(\cdot,t) \to f$ in $L^{2}$ as $t \to 0^{+}$.**

$||u(\cdot,t) - f||_{2}^{2} = ||\hat{G}_{t} \hat{f} - \hat{f}||_{2}^{2} = \int |e^{-4\pi^{2}|\xi|^{2}t} - 1|^{2} |\hat{f}(\xi)|^{2} d\xi$.

The integrand converges to 0 pointwise ($e^{-4\pi^{2}|\xi|^{2}t} \to 1$ for each $\xi$) and is bounded by $4|\hat{f}(\xi)|^{2} \in L^{1}$ (since $|e^{-s}-1| \leq 2$). By DCT: $\int \to 0$, so $||u(\cdot,t)-f||_{2} \to 0$. ✓ ∎

**What connects.** $u(x,t)$ is the solution to the heat equation $\partial_{t}u = \Delta u$ with initial data $u(\cdot,0) = f$. The three parts verify the well-posedness: (a) the solution is smooth for $t > 0$ (instantaneous regularisation — a hallmark of parabolic equations), (b) the $L^{2}$ norm doesn't increase (energy dissipation — the heat equation is contractive), (c) the solution recovers the initial data in $L^{2}$ as $t \to 0^{+}$ (continuity at the initial time). The Fourier-analytic proof is the cleanest because the heat kernel diagonalises in Fourier space: $\hat{G}_{t} = e^{-4\pi^{2}|\xi|^{2}t}$ acts as a multiplier, making all estimates transparent. This is the prototypical approximate identity in $\mathbb{R}^{n}$.

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
- `MeasureTheory.Memℒp f 2 volume` — $f \in L^{2}(\mathbb{R}^{n})$
- `MeasureTheory.eLpNorm` — Lp seminorm
- `ContDiff ℝ ⊤ f` — infinitely smooth ($C^\infty$)
- `HasFDerivAt` — Fréchet differentiability
- `Fin n → ℝ` — $\mathbb{R}^{n}$ with `volume` as Lebesgue measure
- `Filter.𝓝[>] 0` — right-neighbourhood filter

**Key lemmas:**
- `integral_gaussian` — $\int e^{-bx^{2}} = \sqrt{\pi/b}$. For verifying $\int G_t = 1$. In `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`
- Young's inequality — `MeasureTheory.convolution_le_Lp_mul_L1` or similar. For part (b)
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — DCT. For the Fourier-space argument in part (c) and for differentiation under the integral in part (a)
- `ContDiff.integral_clm` — differentiating under the integral sign for parameter-dependent integrals. For part (a)
- `hasDerivAt_integral_of_dominated_convergence` — differentiation under integral. In `Mathlib.MeasureTheory.Integral.DominatedConvergence`
- `Real.exp_neg_mul_sq_le` — Gaussian tail bounds
- `MeasureTheory.Lp.tendsto_approx` — density for approximation arguments

**Tactic hints:**
- `apply ContDiff.integral_clm` — for part (a), differentiating under $\int$
- `exact young_heat_L2 ht hf |>.trans (by simp [heatKernel_integral ht])` — for part (b)
- `apply tendsto_integral_of_dominated_convergence (fun x => 4 * ‖f̂ x‖^2)` — DCT in Fourier for part (c)
- `simp [heatKernel, Real.exp_neg]` — unfolding definitions
- `positivity` — for $t > 0$, $4\pi t > 0$
- `gcongr` — for $\Vert \hat{G}_{t} \cdot \hat{f}\Vert \leq \Vert \hat{f}\Vert$
- `field_simp` — for $(4\pi t)^{-n/2}$ arithmetic
- `exact?` — finding the Gaussian integral or Young's inequality