

This is identical to **apm-a00J05** (with g in place of f, and dt in place of dm(t) — both meaning Lebesgue measure). The solution is the same.

# APM a01A11 = a00J05: Cauchy-type integral over a compact real set

## Why It's Hard

Same difficulty as a00J05: g is defined by a real integral but must be shown complex-analytic; the non-extendability requires extracting a concrete obstruction; and the limit at infinity requires dominated convergence. The function g(z) = ∫\_K 1/(t-z) dt is the Cauchy transform of Lebesgue measure restricted to K.

## The Key Insight

**(a)** Morera + Fubini: for any triangle in ℂ \ K, swap the contour integral with the Lebesgue integral, and apply Cauchy's theorem to the inner integral.

**(b)** If g extended to an entire function, Liouville (since g(z) → 0 at ∞) forces g ≡ 0. But Im g(x+iy) = ∫\_K y/((t-x)²+y²) dt > 0 for y > 0, since the Poisson kernel is strictly positive and m(K) > 0. Contradiction.

**(c)** Factor: zg(z) = ∫\_K z/(t-z) dt = ∫\_K 1/(t/z - 1) dt → ∫\_K (-1) dt = -m(K) by dominated convergence. The limit is **-m(K)**.

## Complete Proof

### Part (a): g is analytic on ℂ \ K

Let Δ be a triangle in ℂ \ K. Since Δ and K are disjoint compact sets, δ := dist(Δ, K) > 0, so |1/(t-z)| ≤ 1/δ for t ∈ K, z ∈ Δ. This uniform bound justifies Fubini:

$$\oint_\Delta g(z)\,dz = \oint_\Delta \int_K \frac{1}{t-z}\,dt\,dz = \int_K \oint_\Delta \frac{1}{t-z}\,dz\,dt = \int_K 0\,dt = 0$$

since z ↦ 1/(t-z) is analytic on ℂ \ {t} ⊇ ℂ \ K ⊇ Δ for each t ∈ K. By Morera's theorem, g is analytic. ∎

The derivative is g'(z) = ∫\_K 1/(t-z)² dt (differentiation under the integral, justified by dominated convergence with the same δ-bound).

### Part (b): g does not extend to an entire function

Suppose F : ℂ → ℂ is entire with F = g on ℂ \ K.

**F is bounded:** For |z| large, |g(z)| ≤ ∫\_K 1/|t-z| dt ≤ m(K)/(|z| - max|K|) → 0. So F is continuous on ℂ (hence bounded on any compact set) and F(z) → 0 as |z| → ∞. By Liouville, F ≡ 0.

**Contradiction via the Poisson kernel:** For x ∈ ℝ, y > 0, z = x + iy ∈ ℂ \ ℝ ⊂ ℂ \ K:

$$\operatorname{Im}\,g(x+iy) = \int_K \frac{y}{(t-x)^2 + y^2}\,dt > 0$$

since the integrand is strictly positive for all t ∈ K and m(K) > 0. But F ≡ 0 gives Im g(x+iy) = 0, a contradiction. ∎

### Part (c): lim\_{z→∞} z·g(z) = -m(K)

$$z\,g(z) = \int_K \frac{z}{t-z}\,dt = \int_K \frac{1}{t/z - 1}\,dt.$$

For t ∈ K (bounded) and |z| → ∞: t/z → 0, so 1/(t/z - 1) → -1 pointwise.

Domination: for |z| > 2 max\_{t∈K} |t|, we have |t/z| ≤ 1/2, so |t/z - 1| ≥ 1/2, giving |1/(t/z-1)| ≤ 2. This integrable bound (2 · m(K) < ∞) justifies dominated convergence:

$$\lim_{|z|\to\infty} z\,g(z) = \int_K (-1)\,dt = -m(K). \qquad \blacksquare$$

## What Connects

Same connections as a00J05: Cauchy transform, potential theory, analytic capacity, Stieltjes transform, moments via the Laurent expansion at ∞.

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

**Mathlib notes:** Identical to a00J05. `cauchyIntegral K z` is the Bochner integral ∫\_K 1/(t-z) dt with `(↑t : ℂ)` embedding ℝ → ℂ. `DifferentiableOn ℂ` encodes holomorphicity. `cocompact ℂ` is the filter for |z| → ∞. The Poisson kernel positivity `cauchyIntegral_im_pos` is the engine of part (b): it produces the contradiction with Liouville. The residue `-(volume.restrict K univ).toReal` equals -m(K) coerced to ℂ.
