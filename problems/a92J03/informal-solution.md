

# APM a92J03: The Fourier transform maps $L^{1}$ to $C_{0}$ (Riemann-Lebesgue)

## 1. Informal proof

**Why it's hard.** Parts (a) and (b) are straightforward applications of dominated convergence and the triangle inequality, but part (c) — showing $\hat{f}(\xi) \to 0$ as $|\xi| \to \infty$ — is the Riemann-Lebesgue lemma, which requires an approximation argument. The decay at infinity comes from oscillatory cancellation, which is invisible to pointwise estimates.

**The key insight.** For a single indicator function $1_{[a,b]}$, the Fourier transform is $(e^{ib\xi} - e^{ia\xi})/(i\xi)$, which is $O(1/|\xi|) \to 0$. This extends by linearity to step functions, and then by density (step functions are dense in $L^{1}$) and the uniform bound $\|\hat{f}\|_\infty \leq \|f\|_{1}$ to all of $L^{1}$.

**Proof.**

**(a) $\hat{f}$ is continuous.** Fix $\xi_{0} \in \mathbb{R}$. For $\xi \to \xi_{0}$:

$|\hat{f}(\xi) - \hat{f}(\xi_{0})| = |\int f(x)(e^{ix\xi} - e^{ix\xi_{0}}) dx| \leq \int |f(x)| \cdot |e^{ix\xi} - e^{ix\xi_{0}}| dx$.

The integrand satisfies $|f(x)(e^{ix\xi} - e^{ix\xi_{0}})| \leq 2|f(x)|$ (integrable dominator) and converges to 0 pointwise (since $e^{ix\xi} \to e^{ix\xi_{0}}$ for each $x$). By the dominated convergence theorem, the integral $\to 0$. ✓

**(b) $\|\hat{f}\|_\infty \leq \|f\|_{1}$.** For any $\xi$:

$|\hat{f}(\xi)| = |\int f(x)e^{ix\xi} dx| \leq \int |f(x)| \cdot |e^{ix\xi}| dx = \int |f(x)| dx = \|f\|_{1}$.

Taking sup over $\xi$ gives $\|\hat{f}\|_\infty \leq \|f\|_{1}$. ✓

**(c) $\hat{f}(\xi) \to 0$ for step functions.** Let $f = \sum_{j=1}^N c_j 1_{[a_j, b_j]}$. Then:

$\hat{f}(\xi) = \sum c_j \int_{a_j}^{b_j} e^{ix\xi} dx = \sum c_j (e^{ib_j\xi} - e^{ia_j\xi})/(i\xi)$.

Each term is $O(1/|\xi|) \to 0$ as $|\xi| \to \infty$. Since the sum is finite, $\hat{f}(\xi) \to 0$. ✓

**Deduction: $\hat{f} \in C_{0}(\mathbb{R})$ for all $f \in L^{1}$.** We show $\hat{f}(\xi) \to 0$ as $|\xi| \to \infty$ for general $f \in L^{1}$. Fix $\varepsilon > 0$. Since step functions (finite linear combinations of interval indicators) are dense in $L^{1}(\mathbb{R})$, choose a step function $s$ with $\|f - s\|_{1} < \varepsilon/2$. Then:

$|\hat{f}(\xi)| \leq |\hat{s}(\xi)| + |(\hat{f} - \hat{s})(\xi)| \leq |\hat{s}(\xi)| + \|f - s\|_{1} < |\hat{s}(\xi)| + \varepsilon/2$.

By part (c), $|\hat{s}(\xi)| < \varepsilon/2$ for $|\xi|$ large enough. So $|\hat{f}(\xi)| < \varepsilon$ for $|\xi|$ large. Combined with parts (a) and (b), $f \mapsto \hat{f}$ is a bounded linear map from $L^{1}(\mathbb{R})$ into $C_{0}(\mathbb{R})$. ✓ ∎

**What connects.** This is the Riemann-Lebesgue lemma, one of the most fundamental results in Fourier analysis. It says the Fourier transform $F : L^{1}(\mathbb{R}) \to C_{0}(\mathbb{R})$ is a bounded linear operator with $\|F\| \leq 1$. The map is injective (by the Fourier inversion theorem) but not surjective (its image is a proper closed subalgebra of $C_{0}$). The proof strategy — verify on a dense subclass, then extend by density using a uniform bound — is the paradigmatic approximation argument in functional analysis. The same argument proves Riemann-Lebesgue on $\mathbb{R}^{n}$, on the circle (where it gives the decay of Fourier coefficients), and in any locally compact abelian group.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Order.Filter.Basic

open MeasureTheory Complex Set Filter Topology

noncomputable section

/-- The Fourier transform: f̂(ξ) = ∫ f(x) e^{ixξ} dx. -/
def fourierTransform (f : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ x, f x * exp (I * x * ξ) ∂volume

/-- (a) The Fourier transform is continuous. -/
theorem fourierTransform_continuous
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (fourierTransform f) := by
  sorry

/-- (b) Sup bound: ‖f̂‖_∞ ≤ ‖f‖₁. -/
theorem fourierTransform_norm_le
    {f : ℝ → ℂ} (hf : Integrable f volume) (ξ : ℝ) :
    ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume := by
  sorry

/-- (c) For interval indicators, f̂(ξ) → 0 as |ξ| → ∞. -/
theorem fourierTransform_indicator_tendsto_zero
    {a b : ℝ} (hab : a < b) :
    Tendsto (fun ξ => fourierTransform (Set.indicator (Icc a b) (fun _ => (1 : ℂ))) ξ)
      (cocompact ℝ) (𝓝 0) := by
  sorry

/-- For finite linear combinations of interval indicators. -/
theorem fourierTransform_step_tendsto_zero
    {n : ℕ} {c : Fin n → ℂ} {a b : Fin n → ℝ}
    (hab : ∀ i, a i < b i) :
    Tendsto (fun ξ => fourierTransform
      (fun x => ∑ i, c i * (Icc (a i) (b i)).indicator (fun _ => (1 : ℂ)) x) ξ)
      (cocompact ℝ) (𝓝 0) := by
  sorry

/-- Step functions are dense in L¹(ℝ). -/
lemma step_functions_dense_L1
    {f : ℝ → ℂ} (hf : Integrable f volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a b : Fin n → ℝ),
      (∀ i, a i < b i) ∧
      ∫ x, ‖f x - ∑ i, c i * (Icc (a i) (b i)).indicator (fun _ => (1 : ℂ)) x‖ < ε := by
  sorry

/-- Riemann-Lebesgue: f̂(ξ) → 0 as |ξ| → ∞ for all f ∈ L¹. -/
theorem riemann_lebesgue
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0) := by
  sorry

/-- Full theorem: the Fourier transform maps L¹ into C₀(ℝ).
    f̂ is continuous, bounded by ‖f‖₁, and vanishes at infinity. -/
theorem fourier_maps_L1_to_C0
    {f : ℝ → ℂ} (hf : Integrable f volume) :
    Continuous (fourierTransform f) ∧
    (∀ ξ, ‖fourierTransform f ξ‖ ≤ ∫ x, ‖f x‖ ∂volume) ∧
    Tendsto (fourierTransform f) (cocompact ℝ) (𝓝 0) := by
  sorry

/-- The Fourier transform as a bounded linear map L¹ → C₀.
    Operator norm ≤ 1. -/
theorem fourierTransform_norm_le_one :
    ∀ (f : ℝ → ℂ), Integrable f volume →
      ∀ ξ, ‖fourierTransform f ξ‖ ≤ ‖∫ x, ‖f x‖ ∂volume‖ := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.Integrable f volume` — $f \in L^{1}(\mathbb{R})$
- `Complex.exp`, `Complex.I` — exponential kernel $e^{ix\xi}$
- `Filter.cocompact ℝ` — filter for $|\xi| \to \infty$
- `Filter.Tendsto` — convergence along a filter
- `Set.indicator` — characteristic function of an interval
- `ContinuousMap.ZeroAtInfty` — the space $C_{0}(\mathbb{R})$ (in `Mathlib.Topology.ContinuousFunction.ZeroAtInfty`)

**Key lemmas:**
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — DCT: the engine of part (a). Pointwise convergence + integrable dominator $\implies$ integral converges
- `MeasureTheory.norm_integral_le_integral_norm` — $|\int f| \leq \int |f|$, the engine of part (b)
- `Complex.norm_exp_ofReal_mul_I` / `Complex.abs_exp_ofReal_mul_I` — $|e^{ix\xi}| = 1$
- `intervalIntegral.integral_exp_mul_complex` — $\int_a^b e^{icx} dx = (e^{icb} - e^{ica})/(ic)$, the engine of part (c)
- `Integrable.sub` — integrability of $f - s$ for the density argument
- `MeasureTheory.SimpleFunc.tendsto_approxOn` / density of step functions in $L^{1}$ — for the approximation step
- `Filter.Tendsto.add` / `Filter.Tendsto.sub` — algebra of limits
- `norm_add_le` — triangle inequality for the $\varepsilon/2$ argument
- `Real.tendsto_inv_atTop_nhds_zero` — $1/|\xi| \to 0$ (for indicator transforms)
- `VectorFourier.fourierIntegral` — Mathlib's Fourier transform definition (in `Mathlib.Analysis.Fourier.FourierTransformDeriv`), which may differ by convention
- `MeasureTheory.Integrable.norm` — $\|f\|$ integrable when $f$ integrable

**Tactic hints:**
- `apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)` — for part (a), applying DCT
- `calc` — for the $\varepsilon/2$ chain in the density argument
- `simp [Complex.norm_exp_ofReal_mul_I]` — simplifying $|e^{ix\xi}| = 1$
- `field_simp` — for $(e^{ib\xi} - e^{ia\xi})/(i\xi)$ manipulations
- `gcongr` — for monotonicity in norm bounds
- `exact norm_integral_le_integral_norm _ _` — for part (b)
- `intro ε hε` — starting the Riemann-Lebesgue $\varepsilon$ argument
- `obtain ⟨s, hs_approx⟩ := step_functions_dense_L1 hf (half_pos hε)` — density
- `linarith` — combining the $\varepsilon/2$ bounds
- `filter_upwards` — for cocompact filter arguments
- `continuity` — establishing continuity of the integrand in $\xi$