This is identical to **apm-a00J05** (with $g$ in place of $f$, and $dt$ in place of $dm(t)$ — both meaning Lebesgue measure). The solution is the same.

# APM a01A11 = a00J05: Cauchy-type integral over a compact real set

## Why It's Hard

Same difficulty as a00J05: $g$ is defined by a real integral but must be shown complex-analytic; the non-extendability requires extracting a concrete obstruction; and the limit at infinity requires dominated convergence. The function $g(z) = \int_K 1/(t-z)\, dt$ is the Cauchy transform of Lebesgue measure restricted to $K$.

## The Key Insight

**(a)** Morera + Fubini: for any triangle in $\mathbb{C} \setminus K$, swap the contour integral with the Lebesgue integral, and apply Cauchy's theorem to the inner integral.

**(b)** If $g$ extended to an entire function, Liouville (since $g(z) \to 0$ at $\infty$) forces $g \equiv 0$. But $\operatorname{Im} g(x+iy) = \int_K y/((t-x)^{2}+y^{2})\, dt > 0$ for $y > 0$, since the Poisson kernel is strictly positive and $m(K) > 0$. Contradiction.

**(c)** Factor: $zg(z) = \int_K z/(t-z)\, dt = \int_K 1/(t/z - 1)\, dt \to \int_K (-1)\, dt = -m(K)$ by dominated convergence. The limit is **$-m(K)$**.

## Complete Proof

### Part (a): $g$ is analytic on $\mathbb{C} \setminus K$

Let $\Delta$ be a triangle in $\mathbb{C} \setminus K$. Since $\Delta$ and $K$ are disjoint compact sets, $\delta := \mathrm{dist}(\Delta, K) > 0$, so $|1/(t-z)| \leq 1/\delta$ for $t \in K$, $z \in \Delta$. This uniform bound justifies Fubini:

$$\oint_\Delta g(z)\,dz = \oint_\Delta \int_K \frac{1}{t-z}\,dt\,dz = \int_K \oint_\Delta \frac{1}{t-z}\,dz\,dt = \int_K 0\,dt = 0$$

since $z \mapsto 1/(t-z)$ is analytic on $\mathbb{C} \setminus \{t\} \supseteq \mathbb{C} \setminus K \supseteq \Delta$ for each $t \in K$. By Morera's theorem, $g$ is analytic. ∎

The derivative is $g'(z) = \int_K 1/(t-z)^{2}\, dt$ (differentiation under the integral, justified by dominated convergence with the same $\delta$-bound).

### Part (b): $g$ does not extend to an entire function

Suppose $F : \mathbb{C} \to \mathbb{C}$ is entire with $F = g$ on $\mathbb{C} \setminus K$.

**$F$ is bounded:** For $|z|$ large, $|g(z)| \leq \int_K 1/|t-z|\, dt \leq m(K)/(|z| - \max|K|) \to 0$. So $F$ is continuous on $\mathbb{C}$ (hence bounded on any compact set) and $F(z) \to 0$ as $|z| \to \infty$. By Liouville, $F \equiv 0$.

**Contradiction via the Poisson kernel:** For $x \in \mathbb{R}$, $y > 0$, $z = x + iy \in \mathbb{C} \setminus \mathbb{R} \subset \mathbb{C} \setminus K$:

$$\operatorname{Im}\,g(x+iy) = \int_K \frac{y}{(t-x)^2 + y^2}\,dt > 0$$

since the integrand is strictly positive for all $t \in K$ and $m(K) > 0$. But $F \equiv 0$ gives $\operatorname{Im} g(x+iy) = 0$, a contradiction. ∎

### Part (c): $\lim_{z\to\infty} z\cdot g(z) = -m(K)$

$$z\,g(z) = \int_K \frac{z}{t-z}\,dt = \int_K \frac{1}{t/z - 1}\,dt.$$

For $t \in K$ (bounded) and $|z| \to \infty$: $t/z \to 0$, so $1/(t/z - 1) \to -1$ pointwise.

Domination: for $|z| > 2 \max_{t\in K} |t|$, we have $|t/z| \leq 1/2$, so $|t/z - 1| \geq 1/2$, giving $|1/(t/z-1)| \leq 2$. This integrable bound ($2 \cdot m(K) < \infty$) justifies dominated convergence:

$$\lim_{|z|\to\infty} z\,g(z) = \int_K (-1)\,dt = -m(K). \qquad \blacksquare$$

## What Connects

Same connections as a00J05: Cauchy transform, potential theory, analytic capacity, Stieltjes transform, moments via the Laurent expansion at $\infty$.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic

open MeasureTheory Complex Set Filter Topology

noncomputable section

variable {K : Set ℝ} (hK : IsCompact K) (hKpos : 0 < volume K)

/-- The Cauchy-type integral g(z) = ∫_K 1/(t - z) dt. -/
def cauchyIntegral (K : Set ℝ) (z : ℂ) : ℂ :=
  ∫ t in K, (1 : ℂ) / (↑t - z) ∂volume

/-- The integrand is integrable when z ∉ K (embedded in ℂ). -/
lemma cauchyIntegral_integrableOn
    (hK : IsCompact K) {z : ℂ} (hz : z ∉ ofReal '' K) :
    IntegrableOn (fun t : ℝ => (1 : ℂ) / (↑t - z)) K volume := by
  sorry

/-- Part (a): g is holomorphic on ℂ \ K. -/
theorem cauchyIntegral_differentiableOn (hK : IsCompact K) :
    DifferentiableOn ℂ (cauchyIntegral K) (ofReal '' K)ᶜ := by
  sorry

/-- The derivative: g'(z) = ∫_K 1/(t-z)² dt. -/
theorem hasDeriv_cauchyIntegral (hK : IsCompact K)
    {z : ℂ} (hz : z ∉ ofReal '' K) :
    HasDerivAt (cauchyIntegral K)
      (∫ t in K, (1 : ℂ) / (↑t - z) ^ 2 ∂volume) z := by
  sorry

/-- g(z) → 0 as |z| → ∞. -/
theorem cauchyIntegral_tendsto_zero (hK : IsCompact K) :
    Tendsto (cauchyIntegral K) (cocompact ℂ) (𝓝 0) := by
  sorry

/-- Part (b), key step: Im g(x+iy) > 0 for y > 0
    (Poisson kernel is strictly positive on K). -/
lemma cauchyIntegral_im_pos
    (hK : IsCompact K) (hKpos : 0 < volume K)
    {x y : ℝ} (hy : 0 < y) :
    0 < (cauchyIntegral K (↑x + ↑y * I)).im := by
  sorry

/-- Part (b): g does not extend to an entire function. -/
theorem cauchyIntegral_not_entire
    (hK : IsCompact K) (hKpos : 0 < volume K) :
    ¬ ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      ∀ z ∉ ofReal '' K, F z = cauchyIntegral K z := by
  sorry

/-- Part (c): z · g(z) → -m(K) as |z| → ∞. -/
theorem cauchyIntegral_residue_at_infinity
    (hK : IsCompact K) (hKpos : 0 < volume K) :
    Tendsto (fun z => z * cauchyIntegral K z)
      (cocompact ℂ)
      (𝓝 (-(volume.restrict K Set.univ).toReal : ℂ)) := by
  sorry

/-- Dominated convergence input for part (c):
    |1/(t/z - 1)| ≤ 2 when |z| is large relative to K. -/
lemma integrand_dominated (hK : IsCompact K)
    {R : ℝ} (hR : 2 * sSup (abs '' K) < R) :
    ∀ t ∈ K, ∀ z : ℂ, R < ‖z‖ →
      ‖(1 : ℂ) / ((↑t : ℂ) / z - 1)‖ ≤ 2 := by
  sorry

end
```

**Mathlib notes:** Identical to a00J05. `cauchyIntegral K z` is the Bochner integral $\int_K 1/(t-z)\, dt$ with `(↑t : ℂ)` embedding $\mathbb{R} \to \mathbb{C}$. `DifferentiableOn ℂ` encodes holomorphicity. `cocompact ℂ` is the filter for $|z| \to \infty$. The Poisson kernel positivity `cauchyIntegral_im_pos` is the engine of part (b): it produces the contradiction with Liouville. The residue `-(volume.restrict K univ).toReal` equals $-m(K)$ coerced to $\mathbb{C}$.
