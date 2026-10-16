

# APM a94A03: Gaussian convolution is an Lp contraction and approximate identity

## 1. Informal proof

**Why it's hard.** Part (a) requires showing $||K_t f||_p \leq ||f||_p$ — a convolution norm bound that for general $p$ requires Young's inequality (not just Hölder). Part (b) requires Lp convergence of convolutions to the identity, which needs density of nice functions + the contraction bound from (a).

**The key insight.** The kernel $\phi_t(x) = (1/t)e^{-\pi x^{2}/t^{2}}$ is a Gaussian approximate identity: it has $\int\phi_t = 1$ (after checking the normalisation), so $K_t f = \phi_t * f$. Young's inequality with $||\phi_t||_{1} = 1$ gives $||K_t f||_p \leq ||\phi_t||_{1} \cdot ||f||_p = ||f||_p$. For (b), approximate $f$ by continuous compactly supported $g$, use $||K_t f - f||_p \leq ||K_t(f-g)||_p + ||K_t g - g||_p \leq ||f-g||_p + ||K_t g - g||_p$, and the second term $\to 0$ by uniform convergence of $K_t g$ to $g$.

**Proof.**

*Step 0: Verify $\int\phi_t = 1$.* $\phi_t(x) = (1/t)e^{-\pi x^{2}/t^{2}}$. Substituting $u = \sqrt{\pi} x/t$: $\int\phi_t dx = (1/t)\cdot(t/\sqrt{\pi})\cdot\int e^{-u^{2}}du = (1/\sqrt{\pi})\cdot\sqrt{\pi} = 1$. ✓

**(a) $||K_t f||_p \leq ||f||_p$.**

$K_t f = \phi_t * f$ where $\phi_t \in L^{1}$ with $||\phi_t||_{1} = 1$ and $\phi_t \geq 0$. By Young's convolution inequality ($||g*h||_p \leq ||g||_{1} \cdot ||h||_p$):

$||K_t f||_p = ||\phi_t * f||_p \leq ||\phi_t||_{1} \cdot ||f||_p = 1 \cdot ||f||_p = ||f||_p$.

So $K_t$ maps the unit ball of Lp into itself. ✓

**(b) $||K_t f - f||_p \to 0$ as $t \to 0$.**

Since $\int\phi_t = 1$: $K_t f(x) - f(x) = \int\phi_t(y)[f(x-y) - f(x)]dy$.

By Minkowski's integral inequality (the continuous version):

$||K_t f - f||_p \leq \int|\phi_t(y)| \cdot ||\tau_y f - f||_p dy = \int\phi_t(y) ||\tau_y f - f||_p dy$.

Now $||\tau_y f - f||_p \to 0$ as $y \to 0$ (continuity of Lp translation). Given $\epsilon > 0$, choose $\delta$ such that $||\tau_y f - f||_p < \epsilon$ for $|y| < \delta$. Split:

$\int\phi_t(y)||\tau_y f - f||_p dy = \int_{|y|<\delta} + \int_{|y|\geq\delta}$.

First integral $\leq \epsilon \cdot \int\phi_t = \epsilon$.

Second integral $\leq 2||f||_p \cdot \int_{|y|\geq\delta} \phi_t(y) dy$. Now $\int_{|y|\geq\delta} (1/t)e^{-\pi y^{2}/t^{2}} dy = \int_{|u|\geq\delta/t} (1/\sqrt{\pi})e^{-u^{2}} du \to 0$ as $t \to 0$ (Gaussian tail).

So $||K_t f - f||_p \leq \epsilon + 2||f||_p \cdot o(1) < 2\epsilon$ for $t$ small. ✓ ∎

**What connects.** This is the prototypical approximate identity / mollifier result. The Gaussian kernel $(1/t)e^{-\pi x^{2}/t^{2}}$ is the heat kernel at time $t^{2}/(4\pi)$ — so $K_t f$ solves the heat equation with initial data $f$, and part (b) says the solution converges to the initial data in Lp. Part (a) is a special case of Young's inequality (the case $||\phi||_{1} = 1$), which says convolution with an $L^{1}$ function of norm 1 is an Lp contraction. The same argument works for any approximate identity (Poisson kernel, Fejér kernel, etc.) — the Gaussian is just the smoothest example.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.LpSpace
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Group.Convolution

open MeasureTheory Set Filter Real

noncomputable section

/-- The Gaussian kernel φ_t(x) = (1/t) e^{-π x²/t²}. -/
def gaussKernel (t : ℝ) (x : ℝ) : ℝ :=
  (1 / t) * exp (-π * x ^ 2 / t ^ 2)

/-- The Gaussian convolution operator K_t f = φ_t * f. -/
def gaussConv (t : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y, gaussKernel t (x - y) * f y ∂volume

/-- The Gaussian kernel integrates to 1. -/
lemma gaussKernel_integral_eq_one {t : ℝ} (ht : 0 < t) :
    ∫ x, gaussKernel t x ∂volume = 1 := by
  sorry

/-- The Gaussian kernel is nonneg. -/
lemma gaussKernel_nonneg {t : ℝ} (ht : 0 < t) (x : ℝ) :
    0 ≤ gaussKernel t x := by
  sorry

/-- The Gaussian kernel is in L¹ with norm 1. -/
lemma gaussKernel_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (gaussKernel t) volume := by
  sorry

/-- Gaussian tail: ∫_{|x|≥δ} φ_t(x) dx → 0 as t → 0⁺. -/
lemma gaussKernel_tail_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t => ∫ x in {x : ℝ | δ ≤ |x|},
      gaussKernel t x ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Part (a): K_t is an Lp contraction — ‖K_t f‖_p ≤ ‖f‖_p.
    Follows from Young's inequality with ‖φ_t‖₁ = 1. -/
theorem gaussConv_Lp_contraction
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {t : ℝ} (ht : 0 < t)
    {f : ℝ → ℝ} (hf : Memℒp f p volume) :
    eLpNorm (gaussConv t f) p volume ≤ eLpNorm f p volume := by
  sorry

/-- Part (b): K_t f → f in Lp as t → 0⁺. -/
theorem gaussConv_tendsto_Lp
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume)
    (hfm : AEStronglyMeasurable f volume) :
    Tendsto (fun t => eLpNorm (fun x => gaussConv t f x - f x) p volume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Young's convolution inequality: ‖g * f‖_p ≤ ‖g‖₁ · ‖f‖_p. -/
lemma young_convolution_Lp
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    {g : ℝ → ℝ} (hg : Integrable g volume)
    {f : ℝ → ℝ} (hf : Memℒp f p volume) :
    eLpNorm (fun x => ∫ y, g (x - y) * f y ∂volume) p volume ≤
      eLpNorm g 1 volume * eLpNorm f p volume := by
  sorry

/-- Continuity of Lp translation: ‖τ_h f - f‖_p → 0 as h → 0. -/
lemma Lp_translation_continuous
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {f : ℝ → ℝ} (hf : Memℒp f p volume) :
    Tendsto (fun h : ℝ => eLpNorm (fun x => f (x + h) - f x) p volume)
      (𝓝 0) (𝓝 0) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Memℒp f p volume` — $f \in Lp(\mathbb{R})$
- `MeasureTheory.eLpNorm f p volume` — Lp seminorm
- `MeasureTheory.Integrable f volume` — L¹ membership
- `AEStronglyMeasurable` — measurability
- `Filter.𝓝[>] 0` — right-neighbourhood filter for $t \to 0^{+}$
- `MeasureTheory.convolution` — Mathlib's convolution (in `Mathlib.MeasureTheory.Group.Convolution`)

**Key lemmas:**
- `integral_gaussian` / `integral_gaussian_sq` — $\int e^{-bx^{2}} = \sqrt{\pi/b}$. In `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`. Used to verify $\int\phi_t = 1$
- `MeasureTheory.convolution_le_Lp_mul_L1` — Young's inequality $||g*f||_p \leq ||g||_p \cdot ||f||_{1}$ (or the symmetric version). Would need to verify exact Mathlib name
- `MeasureTheory.norm_integral_le_integral_norm` — $|\int fg| \leq \int |fg|$
- `MeasureTheory.integral_mono` — monotonicity of integrals
- `Real.exp_neg_mul_sq_le` — Gaussian tail bounds
- `tendsto_integral_of_dominated_convergence` — DCT (for proving $K_t g \to g$ when $g$ is nice)
- `MeasureTheory.Lp.tendsto_approx` / density of Cc in Lp — for approximating $f$ by nice functions in part (b)

**Tactic hints:**
- `calc eLpNorm (gaussConv t f) p volume ≤ ...` — for the Young chain
- `intro ε hε` — for the $\epsilon$-$\delta$ argument in part (b)
- `obtain ⟨g, hg_supp, hg_approx⟩ := ...` — approximating $f$ by Cc function
- `gcongr` — for monotonicity-based norm bounds
- `positivity` — for $t > 0$, $\pi > 0$, $\exp > 0$
- `simp [gaussKernel]` — unfolding the kernel definition
- `field_simp` — for $(1/t) \cdot t = 1$ type simplifications
- `nlinarith [Real.sq_sqrt ...]` — for Gaussian integral normalisation arithmetic
- `linarith` — combining the $\epsilon/2$ bounds in the approximation argument
- `filter_upwards` — for "eventually" arguments with the 𝓝[>] 0 filter