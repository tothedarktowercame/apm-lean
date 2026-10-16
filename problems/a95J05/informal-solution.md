

# APM a95J05: Convergence in measure iff $\int|\operatorname{arctan} f_{n}| \to 0$

## 1. Informal proof

**Why it's hard.** The equivalence connects a topological mode of convergence (in measure) to an integral condition involving a specific nonlinear function (arctan). Neither direction is immediate: convergence in measure doesn't control integrals in general, and integral convergence doesn't control pointwise behaviour without extra structure.

**The key insight.** arctan is bounded ($|\operatorname{arctan} t| < \pi/2$) and continuous with $\operatorname{arctan}(0) = 0$, and $|\operatorname{arctan} t| > 0$ iff $t \neq 0$. On a *finite* measure space, convergence in measure is equivalent to convergence in the metric $d(f,g) = \int \phi(|f-g|) d\mu$ for any bounded continuous function $\phi$ with $\phi(0) = 0$ and $\phi(t) > 0$ for $t > 0$. Here $\phi = |\operatorname{arctan}|$ serves this role.

**Proof.**

**($\Longrightarrow$) Convergence in measure $\Longrightarrow \int|\operatorname{arctan} f_{n}| \to 0$.**

Fix $\varepsilon > 0$. Since $|\operatorname{arctan} t| < \pi/2$ for all $t$:

$\int |\operatorname{arctan} f_{n}| = \int_{|f_{n}|\leq\delta} |\operatorname{arctan} f_{n}| + \int_{|f_{n}|>\delta} |\operatorname{arctan} f_{n}|$

$\leq \operatorname{arctan}(\delta) \cdot \mu(\Omega) + (\pi/2) \cdot \mu(\{|f_{n}| > \delta\})$.

Choose $\delta$ small enough that $\operatorname{arctan}(\delta) \cdot \mu(\Omega) < \varepsilon/2$. Then choose $N$ such that $\mu(\{|f_{n}| > \delta\}) < \varepsilon/\pi$ for $n \geq N$ (by convergence in measure). Then $\int|\operatorname{arctan} f_{n}| < \varepsilon/2 + \varepsilon/2 = \varepsilon$. ✓

**($\Longleftarrow$) $\int|\operatorname{arctan} f_{n}| \to 0 \Longrightarrow$ convergence in measure.**

Fix $\varepsilon > 0$. For any $\delta > 0$:

$\int |\operatorname{arctan} f_{n}| \geq \int_{|f_{n}|>\varepsilon} |\operatorname{arctan} f_{n}| \geq \operatorname{arctan}(\varepsilon) \cdot \mu(\{|f_{n}| > \varepsilon\})$.

So $\mu(\{|f_{n}| > \varepsilon\}) \leq \int|\operatorname{arctan} f_{n}| / \operatorname{arctan}(\varepsilon)$.

Since $\int|\operatorname{arctan} f_{n}| \to 0$ and $\operatorname{arctan}(\varepsilon) > 0$ (for $\varepsilon > 0$):

$\mu(\{|f_{n}| > \varepsilon\}) \to 0$. ✓ ∎

**What connects.** This characterises convergence in measure via integrals of bounded continuous "gauge functions." The function $\phi(t) = |\operatorname{arctan} t|$ works because it satisfies three properties: (1) $\phi$ is bounded ($< \pi/2$), which controls the large-deviation term; (2) $\phi(0) = 0$, making the integral small when $f_{n}$ is small; (3) $\phi(t) > 0$ for $t > 0$, ensuring the integral detects nonzero values. Any function with these properties (e.g., $t/(1+t)$, $\min(t,1)$) would work equally well. The equivalence holds specifically on *finite* measure spaces — on infinite measure spaces, convergence in measure is not metrizable by a single integral condition. This result connects to the Ky Fan metric $d(f,g) = \int \min(|f-g|, 1) d\mu$ (or $\int |f-g|/(1+|f-g|) d\mu$), which metrises convergence in measure on finite measure spaces.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open MeasureTheory Filter Real

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Convergence in measure: μ({|fₙ| > ε}) → 0 for all ε > 0. -/
def TendstoInMeasureZero (f : ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => μ {x | ε < |f n x|}) atTop (𝓝 0)

/-- Main theorem: convergence in measure to 0 iff ∫|arctan fₙ| → 0. -/
theorem tendstoInMeasure_iff_integral_arctan
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n)) :
    TendstoInMeasureZero f μ ↔
      Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0) := by
  sorry

/-- (⟹) Convergence in measure implies ∫|arctan fₙ| → 0. -/
theorem integral_arctan_tendsto_of_tendstoInMeasure
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hconv : TendstoInMeasureZero f μ) :
    Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0) := by
  sorry

/-- (⟸) ∫|arctan fₙ| → 0 implies convergence in measure. -/
theorem tendstoInMeasure_of_integral_arctan_tendsto
    {f : ℕ → Ω → ℝ}
    (hf : ∀ n, Measurable (f n))
    (hint : Tendsto (fun n => ∫ x, |arctan (f n x)| ∂μ) atTop (𝓝 0)) :
    TendstoInMeasureZero f μ := by
  sorry

/-- Markov-type bound: μ({|fₙ| > ε}) ≤ ∫|arctan fₙ| / arctan(ε). -/
lemma measure_gt_le_integral_arctan_div
    {f : Ω → ℝ} (hf : Measurable f)
    {ε : ℝ} (hε : 0 < ε) :
    μ {x | ε < |f x|} ≤
      ENNReal.ofReal ((∫ x, |arctan (f x)| ∂μ) / arctan ε) := by
  sorry

/-- arctan is bounded: |arctan t| < π/2 for all t. -/
lemma abs_arctan_lt_pi_div_two (t : ℝ) :
    |arctan t| < π / 2 := by
  sorry

/-- Splitting bound: ∫|arctan fₙ| ≤ arctan(δ)·μ(Ω) + (π/2)·μ({|fₙ|>δ}). -/
lemma integral_arctan_split
    {f : Ω → ℝ} (hf : Measurable f)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫ x, |arctan (f x)| ∂μ) ≤
      arctan δ * (μ Set.univ).toReal +
      (π / 2) * (μ {x | δ < |f x|}).toReal := by
  sorry

/-- arctan is monotone and arctan(0) = 0. -/
lemma arctan_zero : arctan 0 = 0 := by
  sorry

lemma arctan_pos {t : ℝ} (ht : 0 < t) : 0 < arctan t := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `MeasureTheory.IsFiniteMeasure μ` — finite measure space ($\mu(\Omega) < \infty$)
- `MeasureTheory.Measure` — the measure
- `Measurable f` — measurability of $f_{n}$
- `Filter.Tendsto`, `Filter.atTop` — convergence along $\mathbb{N}$
- `ENNReal` — extended nonneg reals for measure values

**Key lemmas:**
- `MeasureTheory.meas_ge_le_mul_pow_snorm` / Markov/Chebyshev — $\mu(\{|f|>\varepsilon\}) \leq \int g(|f|)/g(\varepsilon)$ for monotone $g$. Core of the ($\Longleftarrow$) direction
- `MeasureTheory.integral_mono` — monotonicity of integrals (for splitting)
- `MeasureTheory.integral_add_compl` — $\int = \int_{|f|\leq\delta} + \int_{|f|>\delta}$
- `MeasureTheory.set_integral_le_integral` — $\int_E |g| \leq \int |g|$
- `Real.arctan_zero` — $\operatorname{arctan}(0) = 0$
- `Real.arctan_lt_pi_div_two` — $\operatorname{arctan}(t) < \pi/2$
- `Real.arctan_strictMono` — arctan is strictly monotone
- `Continuous.arctan` / `Real.continuous_arctan` — arctan is continuous (for measurability of composition)
- `Measurable.arctan` — $\operatorname{arctan} \circ f$ is measurable when $f$ is
- `ENNReal.ofReal_div_of_pos` — for the division in the Markov bound
- `IsFiniteMeasure.measure_univ_lt_top` — $\mu(\Omega) < \infty$

**Tactic hints:**
- `constructor` — splitting the iff
- `intro ε hε` — for the $\varepsilon$ argument in convergence in measure
- `calc μ {x | ε < |f n x|} ≤ ... ≤ ∫|arctan fₙ| / arctan ε` — Markov chain for ($\Longleftarrow$)
- `calc ∫|arctan fₙ| ≤ arctan(δ)·μ(Ω) + (π/2)·μ({|fₙ|>δ}) < ε/2 + ε/2` — split for ($\Longrightarrow$)
- `gcongr` — for monotonicity of arctan
- `positivity` — for $\operatorname{arctan}(\varepsilon) > 0$
- `linarith [abs_arctan_lt_pi_div_two (f n x)]` — bounding $|\operatorname{arctan} f| < \pi/2$
- `exact?` — finding the Markov inequality or integral splitting lemma
- `simp [arctan_zero]` — simplifying arctan at 0