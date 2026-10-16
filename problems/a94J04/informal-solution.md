
# APM a94J04: Poisson kernel on the half-plane — $L^{2}$ contraction and approximate identity

## 1. Informal proof

**Why it's hard.** The Poisson kernel $P_y(x) = (1/\pi)y/(y^{2}+x^{2})$ is an approximate identity as $y \to 0^{+}$, but proving the $L^{2}$ operator norm bound requires either Young's inequality (which gives $||P_y||_{1} \leq 1$ for any $p$) or Fourier analysis (where the Poisson kernel has a clean transform). Part (c) about a.e. convergence requires the Hardy-Littlewood maximal inequality, which is significantly deeper than $L^{2}$ convergence.

**The key insight.** The Poisson kernel is a probability measure ($\int P_y = 1$) and a convolution kernel, so $P_y f = P_y * f$. Young's inequality with $||P_y||_{1} = 1$ gives $||P_y f||_{2} \leq ||f||_{2}$. The $L^{2}$ convergence follows from the approximate identity theory. A.e. convergence holds by the maximal theorem.

**Proof.**

**(a) $||P_y f||_{2} \leq ||f||_{2}$.**

The Poisson kernel $P_y(x) = (1/\pi)y/(y^{2}+x^{2})$ satisfies:
- $P_y \geq 0$ everywhere.
- $\int_{-\infty}^{\infty} P_y(x) dx = (1/\pi)\int y/(y^{2}+x^{2}) dx = (1/\pi)[\operatorname{arctan}(x/y)]_{-\infty}^{\infty} = (1/\pi)\cdot\pi = 1$.

So $P_y \in L^{1}(\mathbb{R})$ with $||P_y||_{1} = 1$. The operator $P_y f = P_y * f$ (convolution). By Young's convolution inequality ($||g*f||_{2} \leq ||g||_{1} \cdot ||f||_{2}$):

$||P_y f||_{2} = ||P_y * f||_{2} \leq ||P_y||_{1} \cdot ||f||_{2} = 1 \cdot ||f||_{2} = ||f||_{2}$. ✓

**(b) $||P_y f - f||_{2} \to 0$ as $y \to 0^{+}$.**

Since $P_y$ is a nonneg approximate identity ($\int P_y = 1$, $P_y \geq 0$, and for any $\delta > 0$, $\int_{|t|>\delta} P_y(t)dt \to 0$ as $y \to 0^{+}$), the standard approximate identity convergence theorem gives:

$P_y f \to f$ in $L^{2}$ as $y \to 0^{+}$.

In detail: $||P_y f - f||_{2} = ||\int P_y(t)(f(\cdot-t) - f(\cdot))dt||_{2} \leq \int P_y(t) ||\tau_t f - f||_{2} dt$ (Minkowski integral inequality). Split at $|t| = \delta$: the near part $\leq \sup_{|t|<\delta} ||\tau_t f - f||_{2}$ (which $\to 0$ by $L^{2}$ translation continuity), and the far part $\leq 2||f||_{2} \cdot \int_{|t|>\delta} P_y(t)dt \to 0$ as $y \to 0$. ✓

**(c) A.e. convergence.**

$P_y f(x) \to f(x)$ for a.e. $x$ as $y \to 0^{+}$. This follows from the fact that the Poisson maximal function $P*f(x) = \sup_{y>0} |P_y f(x)|$ is bounded by the Hardy-Littlewood maximal function $Mf(x)$ (since the Poisson kernel is bounded by a radially decreasing $L^{1}$ majorant), and the maximal inequality $||Mf||_{2} \leq C||f||_{2}$ gives $P*f \in L^{2}$ and hence $P*f < \infty$ a.e. The a.e. convergence then follows from the $L^{2}$ convergence (part b) plus the maximal bound via the standard "almost everywhere from $L^{2}$" argument: approximate $f$ by continuous compactly supported $g$ (for which $P_y g \to g$ pointwise everywhere), and control the remainder via the maximal inequality. ✓ ∎

**What connects.** This is the theory of the Poisson integral for the upper half-plane. $P_y f$ is the harmonic extension of $f$ to the upper half-plane: $u(x,y) = P_y f(x)$ solves $\Delta u = 0$ with boundary data $u(x,0) = f(x)$. Part (a) says the boundary-to-interior operator is an $L^{2}$ contraction; part (b) says the solution converges to its boundary data in $L^{2}$; part (c) — the deepest — says convergence holds a.e., which is equivalent to the nontangential convergence of harmonic functions (Fatou's theorem). The Fourier transform provides an alternative proof of (a): $\hat{P}_y(\xi) = e^{-2\pi|\xi|y}$, so $||P_y f||_{2} = ||\hat{P}_y \cdot \hat{f}||_{2} \leq ||\hat{f}||_{2} = ||f||_{2}$ by Plancherel, since $|\hat{P}_y| \leq 1$.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory Set Filter Real

noncomputable section

/-- The Poisson kernel P_y(x) = (1/π) y/(y² + x²). -/
def poissonKernel (y : ℝ) (x : ℝ) : ℝ :=
  (1 / π) * y / (y ^ 2 + x ^ 2)

/-- The Poisson convolution P_y f. -/
def poissonConv (y : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, poissonKernel y (x - t) * f t ∂volume

/-- The Poisson kernel integrates to 1. -/
lemma poissonKernel_integral {y : ℝ} (hy : 0 < y) :
    ∫ x, poissonKernel y x ∂volume = 1 := by
  sorry

/-- The Poisson kernel is nonneg. -/
lemma poissonKernel_nonneg {y : ℝ} (hy : 0 < y) (x : ℝ) :
    0 ≤ poissonKernel y x := by
  sorry

/-- The Poisson kernel is in L¹ with norm 1. -/
lemma poissonKernel_integrable {y : ℝ} (hy : 0 < y) :
    Integrable (poissonKernel y) volume := by
  sorry

/-- The Poisson tail vanishes: ∫_{|t|>δ} P_y(t) → 0 as y → 0⁺. -/
lemma poissonKernel_tail_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun y => ∫ t in {t | δ ≤ |t|},
      poissonKernel y t ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Part (a): P_y is an L² contraction. -/
theorem poissonConv_L2_contraction
    {y : ℝ} (hy : 0 < y)
    {f : ℝ → ℝ} (hf : Memℒp f 2 volume) :
    eLpNorm (poissonConv y f) 2 volume ≤
      eLpNorm f 2 volume := by
  sorry

/-- Part (b): P_y f → f in L² as y → 0⁺. -/
theorem poissonConv_tendsto_L2
    {f : ℝ → ℝ} (hf : Memℒp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    Tendsto (fun y => eLpNorm (fun x => poissonConv y f x - f x) 2 volume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Part (c): P_y f → f a.e. as y → 0⁺.
    Follows from the maximal inequality. -/
theorem poissonConv_tendsto_ae
    {f : ℝ → ℝ} (hf : Memℒp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun y => poissonConv y f x) (𝓝[>] 0) (𝓝 (f x)) := by
  sorry

/-- The Poisson maximal function is bounded by C · Hardy-Littlewood Mf. -/
lemma poisson_maximal_le_hardy_littlewood
    {f : ℝ → ℝ} (hf : Memℒp f 2 volume)
    (hfm : AEStronglyMeasurable f volume) :
    ∀ᵐ x ∂volume,
      sSup {|poissonConv y f x| | y ∈ Ioi (0:ℝ)} ≤
        3 * MeasureTheory.maximalFunction volume f 1 x := by
  sorry

/-- Young's inequality: ‖g * f‖₂ ≤ ‖g‖₁ · ‖f‖₂. -/
lemma young_L1_L2
    {g : ℝ → ℝ} (hg : Integrable g volume)
    {f : ℝ → ℝ} (hf : Memℒp f 2 volume) :
    eLpNorm (fun x => ∫ t, g (x - t) * f t ∂volume) 2 volume ≤
      eLpNorm g 1 volume * eLpNorm f 2 volume := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Memℒp f 2 volume` — $f \in L^{2}(\mathbb{R})$
- `MeasureTheory.eLpNorm f p volume` — Lp seminorm
- `AEStronglyMeasurable` — measurability
- `Filter.𝓝[>] 0` — right-neighbourhood filter for $y \to 0^{+}$
- `MeasureTheory.maximalFunction` — Hardy-Littlewood maximal function (may be in `Mathlib.MeasureTheory.Function.MaximalFunction` or similar)

**Key lemmas:**
- `Real.integral_inv_one_add_sq` — $\int 1/(1+x^{2}) dx = \pi$ (for verifying $\int P_y = 1$ after substitution)
- `MeasureTheory.integral_comp_mul_right` — substitution $u = x/y$
- Young's inequality — `MeasureTheory.convolution_le_Lp_mul_L1` or similar (for part a)
- `MeasureTheory.tendsto_set_integral_of_monotone` — for the tail vanishing
- `Lp_translation_continuous` — $||\tau_h f - f||_{2} \to 0$ (continuity of $L^{2}$ translation, for part b)
- `MeasureTheory.strongType_maximalFunction` — maximal inequality $||Mf||_{2} \leq C||f||_{2}$ (for part c)
- `norm_integral_le_integral_norm` — $|\int gf| \leq \int|g||f|$

**Tactic hints:**
- `calc eLpNorm (poissonConv y f) 2 volume = eLpNorm (P_y * f) 2 volume ≤ ...` — for part (a) chain
- `intro ε hε` — for the $\varepsilon$-$\delta$ arguments in parts (b) and (c)
- `gcongr` — for monotonicity bounds
- `positivity` — for $y > 0$, $\pi > 0$, $y^{2}+x^{2} > 0$
- `field_simp` — for the Poisson kernel algebra
- `simp [poissonKernel]` — unfolding definitions
- `filter_upwards` — for a.e. statements
- `exact?` — finding Young's inequality or maximal function lemma