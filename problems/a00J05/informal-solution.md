

# APM a00J05: Cauchy-type integral over a compact real set

## Why It's Hard

This problem sits at the intersection of complex analysis and real measure theory. The function f is defined by a real integral but must be shown to be complex-analytic — so you need to move derivatives inside an integral sign, which requires uniform convergence arguments. Part (b) is the subtlest: you must show an analytic function defined on ℂ \ K *cannot* extend to all of ℂ, which means extracting a concrete obstruction from the integral representation. Part (c) is the payoff: the behaviour at infinity reveals what f "looks like from far away."

## The Key Insight

**(a)** Differentiate under the integral sign. The integrand 1/(t - z) is holomorphic in z for each fixed t ∈ K, and the derivative ∂/∂z [1/(t-z)] = 1/(t-z)² is uniformly bounded on compact subsets of ℂ \ K, so Leibniz's rule (or Morera's theorem + Fubini) gives holomorphicity.

**(b)** If f extended to an entire function, it would be bounded (since f(z) → 0 as |z| → ∞ by part (c)), hence constant by Liouville, hence zero. But the imaginary part of f jumps across K: for t₀ in the interior of K, the Sokhotski-Plemelj formula shows Im f has a nonzero limit from above vs below. Alternatively: if f ≡ 0 on ℂ \ K, then for x ∈ ℝ \ K, ∫_K 1/(t-x) dm(t) = 0 for all such x, which by the Stieltjes inversion formula forces m(K) = 0, contradicting the hypothesis.

**(c)** Factor out 1/z: zf(z) = z ∫_K 1/(t-z) dm(t) = ∫_K z/(t-z) dm(t) = ∫_K 1/((t/z) - 1) dm(t) → ∫_K (-1) dm(t) = -m(K) as |z| → ∞ (since t/z → 0 for bounded t). So the limit of zf(z) is **-m(K)**, the negative of the Lebesgue measure of K.

## Complete Proof

### Part (a): f is holomorphic on ℂ \ K

**Proof via Morera's theorem.** Let Δ be any triangle contained in ℂ \ K. We need to show ∮_Δ f(z) dz = 0. By Fubini's theorem:

$$\oint_\Delta f(z)\,dz = \oint_\Delta \left(\int_K \frac{1}{t-z}\,dm(t)\right) dz = \int_K \left(\oint_\Delta \frac{1}{t-z}\,dz\right) dm(t).$$

Fubini applies because for z ∈ Δ and t ∈ K, since Δ and K are disjoint compact sets, dist(Δ, K) > 0, so |1/(t-z)| ≤ 1/dist(Δ,K) is uniformly bounded, making the integrand in L^1 of the product measure.

For each fixed t ∈ K, the function z ↦ 1/(t-z) is holomorphic on ℂ \ {t} ⊇ ℂ \ K ⊇ Δ. By Cauchy's theorem, ∮_Δ 1/(t-z) dz = 0.

Therefore ∮_Δ f(z) dz = ∫_K 0 \, dm(t) = 0. By Morera's theorem, f is holomorphic on ℂ \ K. ∎

**Alternative (direct).** For z₀ ∈ ℂ \ K, the difference quotient satisfies:

$$\frac{f(z) - f(z_0)}{z - z_0} = \int_K \frac{1}{(t-z)(t-z_0)}\,dm(t) \to \int_K \frac{1}{(t-z_0)^2}\,dm(t) \quad \text{as } z \to z_0$$

by dominated convergence (the integrand is bounded by 1/dist(z₀,K)² for z close enough to z₀). So f'(z₀) = ∫_K 1/(t-z₀)² dm(t).

### Part (b): f does not extend to an entire function

**Proof.** Suppose for contradiction that f extends to an entire function F : ℂ → ℂ with F(z) = f(z) for all z ∈ ℂ \ K.

From the definition, for |z| large:

$$|f(z)| = \left|\int_K \frac{1}{t-z}\,dm(t)\right| \leq \int_K \frac{1}{|t-z|}\,dm(t) \leq \frac{m(K)}{|z| - \max_{t \in K}|t|} \to 0 \text{ as } |z| \to \infty.$$

So F is a bounded entire function (it is continuous on ℂ, hence bounded on the compact set {|z| ≤ R} for any R, and |F(z)| → 0 for |z| → ∞). By Liouville's theorem, F is constant. Since F(z) → 0 as |z| → ∞, the constant is 0, so F ≡ 0.

But then f(z) = 0 for all z ∈ ℂ \ K. In particular, for real x ∉ K:

$$\int_K \frac{1}{t - x}\,dm(t) = 0 \quad \text{for all } x \in \mathbb{R} \setminus K.$$

This integral is the Stieltjes transform of the measure m|_K (Lebesgue measure restricted to K). The Stieltjes transform uniquely determines a compactly supported measure: if ∫_K 1/(t-z) dm(t) = 0 for all z ∈ ℂ \ K, then by the Stieltjes inversion formula (or by taking z = x + iy and considering the limit as y → 0⁺ of the imaginary part), the measure m|_K must be the zero measure. This means m(K) = 0, contradicting the hypothesis that K has positive Lebesgue measure.

**More elementary argument for the contradiction.** For x ∈ ℝ \ K and y > 0, consider z = x + iy ∈ ℂ \ ℝ ⊂ ℂ \ K. If f ≡ 0:

$$0 = \operatorname{Im} f(x+iy) = \int_K \frac{y}{(t-x)^2 + y^2}\,dm(t).$$

The integrand is the Poisson kernel, which is strictly positive for t ∈ K. Since m(K) > 0, the integral is strictly positive — contradiction. ∎

### Part (c): lim_{|z|→∞} z f(z) = -m(K)

**Proof.** For |z| large and t ∈ K (so t is bounded):

$$z \cdot f(z) = \int_K \frac{z}{t - z}\,dm(t) = \int_K \frac{1}{t/z - 1}\,dm(t).$$

For each fixed t ∈ K, as |z| → ∞, t/z → 0, so 1/(t/z - 1) → 1/(0 - 1) = -1.

The convergence is dominated: since K ⊂ [-M, M] for some M and |z| > 2M, we have |t/z| ≤ 1/2, so |t/z - 1| ≥ 1/2, giving |1/(t/z - 1)| ≤ 2. This bound is integrable (2 · m(K) < ∞).

By the dominated convergence theorem:

$$\lim_{|z| \to \infty} z f(z) = \int_K (-1)\,dm(t) = -m(K). \qquad \blacksquare$$

## What Connects

**To the Cauchy transform.** f is the *Cauchy transform* of the measure m|_K. This is a fundamental object in complex analysis, potential theory, and approximation theory. It is always holomorphic off the support of the measure, always vanishes at infinity, and its boundary values encode the measure via the Sokhotski-Plemelj formula.

**To potential theory.** log|f| is related to the logarithmic potential of K. The fact that zf(z) → -m(K) means f behaves like -m(K)/z at infinity — the "monopole" term in a multipole expansion. The higher terms in the Laurent expansion at ∞ give f(z) = -m(K)/z - (∫_K t dm(t))/z² - ..., recovering the moments of the measure.

**To rational approximation.** Vitushkin's theorem on rational approximation uses the Cauchy transform as its principal tool. Part (b) — the non-extendability — is what makes K "visible" to complex analysis: the analytic capacity of K is positive precisely because m(K) > 0.

**To the Stieltjes transform.** On the real line, f restricted to ℝ \ K is the Stieltjes transform of m|_K. The injectivity of the Stieltjes transform (used in part (b)) is the analytic backbone of the moment problem.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic

open MeasureTheory Complex Set Filter Topology

noncomputable section

variable {K : Set ℝ} (hK_compact : IsCompact K) (hK_pos : 0 < volume K)

/-- The Cauchy-type integral f(z) = ∫_K 1/(t - z) dm(t),
    where we embed t ∈ ℝ into ℂ via ofReal. -/
def cauchyIntegral (K : Set ℝ) (z : ℂ) : ℂ :=
  ∫ t in K, (1 : ℂ) / (↑t - z) ∂volume

/-- The integrand is integrable for z ∉ K (as a subset of ℂ via ofReal). -/
lemma cauchyIntegral_integrable
    (hK_compact : IsCompact K)
    {z : ℂ} (hz : z ∉ ofReal '' K) :
    IntegrableOn (fun t : ℝ => (1 : ℂ) / (↑t - z)) K volume := by
  sorry

/-- Part (a): The Cauchy integral is holomorphic on ℂ \ K.
    Stated as: f is differentiable at every z not in the image of K. -/
theorem cauchyIntegral_differentiableOn
    (hK_compact : IsCompact K) :
    DifferentiableOn ℂ (cauchyIntegral K) (ofReal '' K)ᶜ := by
  sorry

/-- The derivative of the Cauchy integral is given by
    f'(z) = ∫_K 1/(t - z)² dm(t). -/
theorem hasDeriv_cauchyIntegral
    (hK_compact : IsCompact K)
    {z : ℂ} (hz : z ∉ ofReal '' K) :
    HasDerivAt (cauchyIntegral K)
      (∫ t in K, (1 : ℂ) / (↑t - z) ^ 2 ∂volume) z := by
  sorry

/-- f(z) → 0 as |z| → ∞. -/
theorem cauchyIntegral_tendsto_zero
    (hK_compact : IsCompact K) (hK_pos : 0 < volume K) :
    Tendsto (cauchyIntegral K) (cocompact ℂ) (𝓝 0) := by
  sorry

/-- Part (b), key ingredient: the imaginary part of f(x+iy) is
    strictly positive for y > 0 and m(K) > 0 (Poisson kernel argument). -/
lemma cauchyIntegral_im_pos
    (hK_compact : IsCompact K) (hK_pos : 0 < volume K)
    {x : ℝ} {y : ℝ} (hy : 0 < y) :
    0 < (cauchyIntegral K (↑x + ↑y * I)).im := by
  sorry

/-- Part (b): f does not extend to an entire function.
    Stated as: there is no entire function agreeing with f on ℂ \ K. -/
theorem cauchyIntegral_no_entire_extension
    (hK_compact : IsCompact K) (hK_pos : 0 < volume K) :
    ¬ ∃ (F : ℂ → ℂ), Differentiable ℂ F ∧
      ∀ z ∉ ofReal '' K, F z = cauchyIntegral K z := by
  sorry

/-- Part (c): z · f(z) → -m(K) as |z| → ∞. -/
theorem cauchyIntegral_residue_at_infinity
    (hK_compact : IsCompact K) (hK_pos : 0 < volume K) :
    Tendsto (fun z => z * cauchyIntegral K z)
      (cocompact ℂ) (𝓝 (-(volume K : ℝ≥0∞).toReal)) := by
  sorry

/-- Dominated convergence input: the integrand of z·f(z) is
    uniformly bounded for |z| large. -/
lemma cauchyIntegral_residue_dominated
    (hK_compact : IsCompact K)
    {R : ℝ} (hR : R > 2 * sSup (abs '' K)) :
    ∀ t ∈ K, ∀ z : ℂ, R < ‖z‖ →
      ‖(1 : ℂ) / ((↑t : ℂ) / z - 1)‖ ≤ 2 := by
  sorry

/-- Alternative statement of (c) with explicit real-valued limit. -/
theorem cauchyIntegral_residue_at_infinity'
    (hK_compact : IsCompact K) (hK_pos : 0 < volume K) :
    Tendsto (fun z => z * cauchyIntegral K z)
      (cocompact ℂ)
      (𝓝 (-↑(volume.restrict K Set.univ).toReal : ℂ)) := by
  sorry

end
```

**Mathlib notes:**

- `cauchyIntegral` is defined using the Bochner integral `∫ t in K, ... ∂volume` with the coercion `(↑t : ℂ)` embedding ℝ into ℂ via `Complex.ofReal`.
- `DifferentiableOn ℂ f S` is the standard Mathlib predicate for holomorphicity on S. For part (a), S = (ofReal '' K)ᶜ.
- `cocompact ℂ` is the filter for |z| → ∞ (complements of compact sets). `Tendsto f (cocompact ℂ) (𝓝 c)` says f(z) → c as |z| → ∞.
- `volume K` returns `ℝ≥0∞`; `.toReal` coerces to ℝ for the limit value. Since K is compact with positive measure, `volume K ≠ ⊤` and `.toReal` is well-behaved.
- The Liouville theorem in Mathlib is `Complex.Polynomial.liouville` or `Differentiable.apply_eq_apply_of_bounded`; part (b) chains this with the Poisson kernel positivity.
- `cauchyIntegral_im_pos` is the core of part (b): Im f(x+iy) = ∫_K y/((t-x)²+y²) dm(t) > 0, since the Poisson kernel is strictly positive and m(K) > 0.
