

# APM a01A04: Volume of the unit ball and superexponential decay

## Why It's Hard

The volume of the unit ball in ℝⁿ has a non-obvious recursive structure and decays to zero superexponentially fast in the dimension. The problem guides you through this in three steps, but each requires a different technique: (a) is a Fubini/slicing argument that produces a specific integral recurrence, (b) is an asymptotic analysis of that integral, and (c) combines (b) with the recurrence to get the superexponential decay. The conceptual difficulty is that the unit ball in ℝⁿ⁺¹ is "thinner" relative to ℝⁿ in a way that compounds multiplicatively — each added dimension contributes a shrinking factor.

## The Key Insight

**Slicing.** The (n+1)-dimensional ball is a stack of n-dimensional balls. At height t ∈ [-1,1], the cross-section of B\_{n+1,1} is an n-ball of radius √(1-t²). Its n-volume is (√(1-t²))ⁿ times the volume of the unit n-ball. Integrating over t gives the recurrence with f(t) = √(1-t²).

**Decay of the integral.** ∫\_{-1}^{1} (1-t²)^{n/2} dt → 0 because (1-t²) < 1 for t ≠ 0, and the set {t = 0} has measure zero — so the integrand converges pointwise to 0 on a full-measure set, and dominated convergence applies.

**Superexponential decay.** The recurrence Vol\_{n+1} = Vol\_n · c\_n with c\_n → 0 means the product telescopes: Vol\_n = Vol\_1 · ∏ c\_k, and since c\_k → 0 the product decays faster than any geometric series, killing Aⁿ · Vol\_n for any fixed A.

## Complete Proof

### Part (a): The slicing recurrence

**Claim.** There exists f : ℝ → [0,1] such that m(B\_{n+1,1}) = m(B\_{n,1}) · ∫\_{-∞}^{∞} [f(t)]ⁿ dt.

**Proof.** Write a point in ℝⁿ⁺¹ as (x, t) where x ∈ ℝⁿ and t ∈ ℝ. Then:

$$(x, t) \in B_{n+1,1} \iff |x|^2 + t^2 \leq 1 \iff |x|^2 \leq 1 - t^2.$$

For |t| ≤ 1, this is a ball in ℝⁿ of radius r(t) = √(1-t²). For |t| > 1, the cross-section is empty.

By Fubini's theorem:

$$m(B_{n+1,1}) = \int_{-1}^{1} m_n\left(\{x \in \mathbb{R}^n : |x| \leq \sqrt{1 - t^2}\}\right) dt = \int_{-1}^{1} m(B_{n,\sqrt{1-t^2}})\,dt.$$

By scaling, the volume of a ball of radius r in ℝⁿ is rⁿ · m(B\_{n,1}). So:

$$m(B_{n+1,1}) = \int_{-1}^{1} (\sqrt{1 - t^2})^n \cdot m(B_{n,1})\,dt = m(B_{n,1}) \int_{-1}^{1} (1 - t^2)^{n/2}\,dt.$$

Define **f(t) = √(1-t²)** for |t| ≤ 1 and f(t) = 0 for |t| > 1. Then f : ℝ → [0,1] and [f(t)]ⁿ = (1-t²)^{n/2} for |t| ≤ 1, so:

$$m(B_{n+1,1}) = m(B_{n,1}) \int_{-\infty}^{\infty} [f(t)]^n\,dt. \qquad \blacksquare$$

### Part (b): ∫ [f(t)]ⁿ dt → 0

**Claim.** $\int_{-\infty}^{\infty} [f(t)]^n\,dt \to 0$ as $n \to \infty$.

**Proof.** We have:

$$I_n := \int_{-1}^{1} (1 - t^2)^{n/2}\,dt.$$

The integrand satisfies:

- For t = 0: (1 - 0)^{n/2} = 1 for all n.
- For 0 < |t| < 1: 0 < 1-t² < 1, so (1-t²)^{n/2} → 0 as n → ∞.
- For |t| = 1: (1-t²)^{n/2} = 0 for all n ≥ 1.

So (1-t²)^{n/2} → 0 pointwise for all t ∈ [-1,1] except t = 0 (a set of measure zero).

The integrand is bounded: (1-t²)^{n/2} ≤ 1 for all t ∈ [-1,1] and all n ≥ 0, and the constant function 1 is integrable on [-1,1].

By the dominated convergence theorem:

$$I_n = \int_{-1}^{1} (1-t^2)^{n/2}\,dt \to \int_{-1}^{1} 0\,dt = 0. \qquad \blacksquare$$

**Explicit bound (optional).** For |t| ≥ δ (with 0 < δ < 1), (1-t²)^{n/2} ≤ (1-δ²)^{n/2}. So:

$$I_n \leq 2\delta + 2(1-\delta^2)^{n/2}.$$

Choosing δ = n^{-1/3}, say, both terms → 0, giving an effective rate.

### Part (c): Aⁿ · m(B\_{n,1}) → 0 for any fixed A > 0

**Claim.** For any A > 0, Aⁿ · m(B\_{n,1}) → 0 as n → ∞.

**Proof.** From part (a), define c\_n = I\_n = ∫\_{-1}^{1} (1-t²)^{n/2} dt, so that:

$$m(B_{n+1,1}) = m(B_{n,1}) \cdot c_n.$$

Telescoping:

$$m(B_{n,1}) = m(B_{1,1}) \cdot \prod_{k=1}^{n-1} c_k = 2 \prod_{k=1}^{n-1} c_k$$

(since B\_{1,1} = [-1,1] has measure 2).

Therefore:

$$A^n \cdot m(B_{n,1}) = 2 \cdot A^n \cdot \prod_{k=1}^{n-1} c_k = 2 \cdot \prod_{k=1}^{n-1} (A \cdot c_k) \cdot A.$$

Wait, more carefully: Aⁿ = A · A^{n-1} = A · ∏\_{k=1}^{n-1} A. So:

$$A^n \cdot m(B_{n,1}) = 2A \cdot \prod_{k=1}^{n-1} (A \cdot c_k).$$

Since c\_k → 0 by part (b), there exists K such that c\_k < 1/(2A) for all k ≥ K. Then A · c\_k < 1/2 for k ≥ K. So for n > K:

$$\prod_{k=1}^{n-1} (A \cdot c_k) = \underbrace{\prod_{k=1}^{K} (A \cdot c_k)}_{= C_K, \text{ fixed}} \cdot \prod_{k=K+1}^{n-1} (A \cdot c_k) \leq C_K \cdot \left(\frac{1}{2}\right)^{n-1-K}.$$

Since (1/2)^{n-1-K} → 0 as n → ∞:

$$A^n \cdot m(B_{n,1}) \leq 2A \cdot C_K \cdot 2^{K} \cdot 2^{-(n-1)} \to 0. \qquad \blacksquare$$

**Interpretation.** The volume of the unit ball decays faster than any exponential r⁻ⁿ. Equivalently, for the ball of radius R in ℝⁿ, Rⁿ · Vol(B\_{n,1}) → 0 for any fixed R: even a ball whose radius grows proportionally to the dimension has volume tending to zero. This is the "curse of dimensionality" — high-dimensional volume concentrates near the equator, and the ball becomes an ever-thinner object.

## What Connects

**To the Gamma function.** The exact volume is m(B\_{n,1}) = πⁿ/² / Γ(n/2 + 1). Stirling's approximation gives Γ(n/2+1) ~ √(πn)(n/(2e))^{n/2}, so m(B\_{n,1}) ~ (2πe/n)^{n/2} / √(πn) — superexponential decay in n, confirming part (c).

**To concentration of measure.** The fact that the integral I\_n = ∫(1-t²)^{n/2} dt → 0 is a manifestation of measure concentration: the mass of the unit ball in ℝⁿ⁺¹ concentrates near the equatorial slice t = 0, with the projections onto the t-axis becoming ever more peaked.

**To the Wallis integral.** I\_n = ∫\_{-1}^{1}(1-t²)^{n/2}dt = B(1/2, n/2+1) = √π · Γ(n/2+1)/Γ(n/2+3/2), which is a beta function. For integer n, this reduces to the Wallis integrals.

**To high-dimensional probability.** In machine learning and statistics, the superexponential volume decay means that in high dimensions, almost all the volume of a cube [-1,1]ⁿ lies outside the inscribed ball — data points are overwhelmingly in the "corners."

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Order.Filter.Basic

open MeasureTheory Set Filter ENNReal Metric

noncomputable section

/-- Volume of the closed unit ball in ℝⁿ, as a function of dimension. -/
def unitBallVolume (n : ℕ) : ℝ≥0∞ :=
  volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)

/-- The cross-section function f(t) = √(1-t²) for |t| ≤ 1, else 0. -/
def crossSectionFn (t : ℝ) : ℝ :=
  if |t| ≤ 1 then Real.sqrt (1 - t ^ 2) else 0

/-- f maps into [0,1]. -/
lemma crossSectionFn_mem_Icc (t : ℝ) :
    crossSectionFn t ∈ Icc (0 : ℝ) 1 := by
  sorry

/-- Part (a): The slicing recurrence.
    Vol(B_{n+1}) = Vol(B_n) · ∫ [f(t)]^n dt. -/
theorem unitBallVolume_succ (n : ℕ) :
    unitBallVolume (n + 1) =
      unitBallVolume n *
        ENNReal.ofReal (∫ t, (crossSectionFn t) ^ n) := by
  sorry

/-- The key integral I_n = ∫_{-1}^{1} (1-t²)^{n/2} dt. -/
def wallis_integral (n : ℕ) : ℝ :=
  ∫ t in Icc (-1 : ℝ) 1, (1 - t ^ 2) ^ (n / 2 : ℝ)

/-- I_n equals ∫ [f(t)]^n dt. -/
lemma wallis_integral_eq (n : ℕ) :
    wallis_integral n = ∫ t, (crossSectionFn t) ^ n := by
  sorry

/-- Part (b): ∫ [f(t)]^n dt → 0 as n → ∞.
    By dominated convergence: the integrand → 0 pointwise a.e.
    on [-1,1] and is bounded by 1. -/
theorem wallis_integral_tendsto_zero :
    Tendsto (fun n => ∫ t, (crossSectionFn t) ^ n) atTop (𝓝 0) := by
  sorry

/-- Pointwise convergence: for t ≠ 0 with |t| ≤ 1,
    (1-t²)^{n/2} → 0 as n → ∞. -/
lemma pointwise_pow_tendsto_zero {t : ℝ} (ht : |t| < 1) (ht0 : t ≠ 0) :
    Tendsto (fun n : ℕ => (1 - t ^ 2) ^ (n / 2 : ℝ)) atTop (𝓝 0) := by
  sorry

/-- Dominated convergence bound: [f(t)]^n ≤ 1 on [-1,1]. -/
lemma crossSectionFn_pow_le_one (t : ℝ) (n : ℕ) :
    (crossSectionFn t) ^ n ≤ 1 := by
  sorry

/-- Part (c): For any A > 0, A^n · Vol(B_n) → 0 as n → ∞.
    Telescoping: Vol(B_n) = Vol(B_1) · ∏_{k=1}^{n-1} c_k where c_k → 0.
    So A^n · Vol(B_n) = const · ∏ (A · c_k), and A · c_k < 1/2 eventually. -/
theorem superexponential_volume_decay (A : ℝ) (hA : 0 < A) :
    Tendsto (fun n => ENNReal.ofReal (A ^ n) * unitBallVolume n)
      atTop (𝓝 0) := by
  sorry

/-- The telescoping product representation. -/
lemma unitBallVolume_product (n : ℕ) (hn : 1 ≤ n) :
    unitBallVolume n =
      unitBallVolume 1 * ∏ k in Finset.range (n - 1),
        ENNReal.ofReal (∫ t, (crossSectionFn t) ^ (k + 1)) := by
  sorry

/-- Eventually, A · c_k < 1/2 for any fixed A. -/
lemma eventually_lt_half (A : ℝ) (hA : 0 < A) :
    ∀ᶠ k in atTop,
      A * (∫ t, (crossSectionFn t) ^ k) < 1 / 2 := by
  sorry

end
```

**Mathlib notes:**

- `EuclideanSpace ℝ (Fin n)` is the standard Mathlib type for ℝⁿ with the Euclidean norm. `Metric.closedBall 0 1` is the closed unit ball, and `volume` gives its Lebesgue measure.
- The slicing/Fubini argument in part (a) uses the fact that `EuclideanSpace ℝ (Fin (n+1)) ≃ EuclideanSpace ℝ (Fin n) × ℝ` and the product measure structure. Mathlib has `MeasureTheory.Measure.pi_eq` and related for product measures.
- `Tendsto ... atTop (𝓝 0)` for `ℝ≥0∞`-valued sequences uses the topology on `ℝ≥0∞`; the neighbourhood filter at 0 includes `[0, ε)` for each ε > 0.
- The finite product `∏ k in Finset.range m, ...` is `Finset.prod`, the standard Mathlib finite product.
- `∀ᶠ k in atTop, P k` means "P holds for all sufficiently large k" — the standard eventually-filter idiom.
