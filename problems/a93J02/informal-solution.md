

# APM a93J02: Σ (-1)ⁿ/(n+1) = log 2 via dominated convergence

## 1. Informal proof

**Why it's hard.** The geometric series 1/(1+x) = Σ (-x)ⁿ converges only for |x| < 1, yet we need to integrate up to x = 1 (where the series converges conditionally but not absolutely). Interchanging the sum and integral requires justification beyond termwise integration of a uniformly convergent series, since the convergence is not uniform on [0,1].

**The key insight.** Integrate the *partial sums* Sₙ(x) = Σₖ₌₀ⁿ (-x)ᵏ = (1-(-x)^{n+1})/(1+x) over [0,1]. Each partial sum is a polynomial (hence integrable), and |Sₙ(x)| ≤ 1/(1-|(-x)|) ... no, we need a uniform dominator. Since |Sₙ(x)| = |1-(-x)^{n+1}|/|1+x| ≤ 2/(1+x) ≤ 2 for x ∈ [0,1], or more simply: each term |(-x)ᵏ| ≤ 1, so |Sₙ(x)| ≤ n+1 — not a fixed bound. Better: use 1/(1+x) directly as the dominator. We have Sₙ(x) → 1/(1+x) pointwise on [0,1), and |Sₙ(x)| ≤ 1/(1-x) is not integrable. Actually |(-x)ᵏ| = xᵏ ≤ 1, so |Sₙ(x)| ≤ (n+1), which is not uniformly bounded. The right approach is different.

**Proof.**

*Step 1: Set up the integral.* We have ∫₀¹ 1/(1+x) dx = log(2).

The geometric series gives, for x ∈ [0,1): 1/(1+x) = Σₙ₌₀^∞ (-1)ⁿxⁿ.

The partial sums are Sₙ(x) = Σₖ₌₀ⁿ (-1)ᵏxᵏ. By direct computation:

∫₀¹ (-1)ᵏxᵏ dx = (-1)ᵏ/(k+1).

So ∫₀¹ Sₙ(x) dx = Σₖ₌₀ⁿ (-1)ᵏ/(k+1).

*Step 2: Apply DCT.* We need to show ∫₀¹ Sₙ(x) dx → ∫₀¹ 1/(1+x) dx.

- **Pointwise convergence:** For each x ∈ [0,1), Sₙ(x) → 1/(1+x) (geometric series).
- **Domination:** |Sₙ(x)| = |1-(-x)^{n+1}|/(1+x) ≤ (1+x^{n+1})/(1+x) ≤ (1+1)/(1+0) = 2 for x ∈ [0,1]. More precisely: |Sₙ(x)| = |(1-(-x)^{n+1})/(1+x)| ≤ 2/(1+x) ≤ 2. The constant function 2 is integrable on [0,1].

By the dominated convergence theorem:

∫₀¹ Sₙ(x) dx → ∫₀¹ 1/(1+x) dx.

*Step 3: Combine.*

Σₖ₌₀ⁿ (-1)ᵏ/(k+1) = ∫₀¹ Sₙ(x) dx → ∫₀¹ 1/(1+x) dx = [log(1+x)]₀¹ = log 2.

Therefore Σₙ₌₀^∞ (-1)ⁿ/(n+1) = log 2. ∎

**What connects.** This is a model application of the DCT to justify termwise integration of a power series at the boundary of its disk of convergence. The Abel summation theorem gives the same result (if Σ aₙ converges and f(x) = Σ aₙxⁿ, then Σ aₙ = lim_{x→1⁻} f(x)), but the DCT approach is more elementary and directly justifies the interchange of sum and integral. The dominator |Sₙ| ≤ 2 comes from the closed-form formula for geometric partial sums, which is the key algebraic input. The same technique proves ∫₀¹ log(1+x)/x dx = π²/12 and many other series-integral identities.

## 2. Lean 4 theorem statement

```lean
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory Set Filter Topology Real

noncomputable section

/-- Main theorem: Σ (-1)ⁿ/(n+1) = log 2. -/
theorem alternating_harmonic_eq_log_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n / (↑n + 1)) (log 2) := by
  sorry

/-- Equivalent tsum formulation. -/
theorem tsum_alternating_harmonic :
    ∑' n : ℕ, (-1 : ℝ) ^ n / (↑n + 1) = log 2 := by
  sorry

/-- ∫₀¹ 1/(1+x) dx = log 2. -/
lemma integral_inv_one_plus :
    ∫ x in (0:ℝ)..1, 1 / (1 + x) = log 2 := by
  sorry

/-- The partial sum Sₙ(x) = Σₖ₌₀ⁿ (-x)ᵏ = (1-(-x)^{n+1})/(1+x). -/
lemma geom_partial_sum (x : ℝ) (hx : x ≠ -1) (n : ℕ) :
    ∑ k in Finset.range (n + 1), (-x) ^ k =
      (1 - (-x) ^ (n + 1)) / (1 + x) := by
  sorry

/-- ∫₀¹ (-1)ᵏ xᵏ dx = (-1)ᵏ/(k+1). -/
lemma integral_pow_term (k : ℕ) :
    ∫ x in (0:ℝ)..1, (-1 : ℝ) ^ k * x ^ k =
      (-1) ^ k / (↑k + 1) := by
  sorry

/-- ∫₀¹ Sₙ(x) dx = Σₖ₌₀ⁿ (-1)ᵏ/(k+1). -/
lemma integral_partial_sum (n : ℕ) :
    ∫ x in (0:ℝ)..1, ∑ k in Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k =
      ∑ k in Finset.range (n + 1), (-1) ^ k / (↑k + 1) := by
  sorry

/-- Domination: |Sₙ(x)| ≤ 2 for x ∈ [0,1]. -/
lemma partial_sum_bound (n : ℕ) (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) :
    |∑ k in Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k| ≤ 2 := by
  sorry

/-- Pointwise convergence: Sₙ(x) → 1/(1+x) for x ∈ [0,1). -/
lemma partial_sum_tendsto (x : ℝ) (hx : x ∈ Ico (0:ℝ) 1) :
    Tendsto (fun n => ∑ k in Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k)
      atTop (𝓝 (1 / (1 + x))) := by
  sorry

/-- DCT application: ∫₀¹ Sₙ → ∫₀¹ 1/(1+x). -/
lemma integral_partial_sum_tendsto :
    Tendsto
      (fun n => ∫ x in (0:ℝ)..1,
        ∑ k in Finset.range (n + 1), (-1 : ℝ) ^ k * x ^ k)
      atTop (𝓝 (∫ x in (0:ℝ)..1, 1 / (1 + x))) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `HasSum f s` — the series Σ f(n) converges to s
- `tsum` — the unconditional sum (when HasSum holds)
- `intervalIntegral` / `∫ x in a..b, f x` — Riemann/Lebesgue integral on intervals
- `Finset.range (n+1)` — the finite set {0, ..., n} for partial sums
- `Filter.atTop` — for n → ∞

**Key lemmas:**
- `MeasureTheory.tendsto_integral_of_dominated_convergence` — DCT: the core tool. Pointwise convergence + integrable dominator ⟹ integral convergence
- `geom_sum_eq` / `Finset.geom_sum` — Σₖ₌₀ⁿ rᵏ = (1 - r^{n+1})/(1-r). In `Mathlib.Algebra.GeomSum`
- `hasSum_geometric_of_abs_lt_one` — Σ rⁿ = 1/(1-r) for |r| < 1
- `intervalIntegral.integral_comp_mul_deriv` — for computing ∫ xᵏ
- `integral_pow` — ∫₀¹ xⁿ dx = 1/(n+1). May be in `Mathlib.Analysis.SpecialFunctions.Integrals`
- `Real.log_eq_integral_inv` — log(b/a) = ∫ₐᵇ 1/x dx (or related FTC form)
- `intervalIntegral.integral_sum` — interchanging finite sum and integral
- `HasSum.tendsto_sum_nat` — relating HasSum to the limit of partial sums
- `abs_neg_one_pow_mul_pow_le` — bounding |(-1)ᵏxᵏ| (may not exist by this name)

**Tactic hints:**
- `apply HasSum.of_tendsto_sum_range` — converting the limit of partial sums to HasSum
- `rw [integral_partial_sum, integral_inv_one_plus]` — chain of equalities
- `apply tendsto_integral_of_dominated_convergence (fun _ => (2:ℝ))` — applying DCT with constant dominator 2
- `simp [Finset.sum_range_succ]` — unfolding partial sums
- `norm_num` — for computing (-1)^k and 1/(k+1)
- `ring` — for algebraic identity (1-(-x)^{n+1})/(1+x)
- `field_simp` — clearing denominators
- `positivity` — for 1+x > 0 on [0,1]
- `gcongr` — for bounding |Sₙ(x)| ≤ 2
- `exact?` — finding the geometric series and integral lemmas