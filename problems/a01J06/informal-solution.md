

# APM a01J06: Convergence exponent of zeros of an entire function of exponential type

## Why It's Hard

The growth condition |f(z)| ≤ Be^{A|z|} (exponential type A) controls how fast f can grow, and this constrains how densely the zeros can accumulate. But converting a *growth bound on the function* into a *convergence statement about the zeros* requires a non-obvious intermediary: Jensen's formula, which relates the modulus of f on circles to the locations of its zeros. The difficulty is that Jensen's formula gives the *count* of zeros n(r) in the disk of radius r, not directly the sum Σ(1+|ωₙ|)^{-α}, so you need to convert a counting function bound into a series convergence statement.

## The Key Insight

**Step 1 (Jensen → counting function bound):** Jensen's formula shows that if |f| ≤ Be^{Ar}, then the number of zeros n(r) in the disk of radius r satisfies n(r) = O(r). Specifically, n(r) ≤ Cr for some constant C.

**Step 2 (Counting function → series convergence):** If n(r) = O(r), then by a summation-by-parts / integral comparison, Σ(1+|ωₙ|)^{-α} converges for α > 1. The idea: there are ~O(r) zeros at distance ~r, each contributing ~r^{-α}, so the total is ~Σ r · r^{-α} = Σ r^{1-α}, which converges for α > 1 (like ∫ r^{1-α} dr).

## Complete Proof

**Theorem.** Let f be entire with |f(z)| ≤ Be^{A|z|}. Let {ωₙ} be the zeros of f listed with multiplicity. Then Σ(1+|ωₙ|)^{-α} < ∞ for all α > 1.

### Step 1: n(r) = O(r) via Jensen's formula

We may assume f(0) ≠ 0 (otherwise, factor out z^m and adjust). Jensen's formula states: for R > 0,

$$\log|f(0)| + \sum_{|\omega_n| < R}\log\frac{R}{|\omega_n|} = \frac{1}{2\pi}\int_0^{2\pi}\log|f(Re^{i\theta})|\,d\theta.$$

The right side satisfies:

$$\frac{1}{2\pi}\int_0^{2\pi}\log|f(Re^{i\theta})|\,d\theta \leq \log(Be^{AR}) = \log B + AR.$$

For the left side, restrict the sum to zeros with |ωₙ| < R/2:

$$\sum_{|\omega_n| < R/2}\log\frac{R}{|\omega_n|} \leq \sum_{|\omega_n| < R}\log\frac{R}{|\omega_n|}.$$

For |ωₙ| < R/2, log(R/|ωₙ|) ≥ log 2. So:

$$n(R/2)\cdot \log 2 \leq \sum_{|\omega_n| < R/2}\log\frac{R}{|\omega_n|} \leq \log B + AR - \log|f(0)|.$$

Therefore:

$$n(R/2) \leq \frac{\log B + AR - \log|f(0)|}{\log 2} \leq C_1 + C_2 R.$$

Setting r = R/2:

$$n(r) \leq C_1 + 2C_2 r \leq C(1 + r)$$

for an appropriate constant C. So **n(r) = O(r)**. ✓

### Step 2: Series convergence via Abel summation

Order the zeros so that |ω₁| ≤ |ω₂| ≤ ···. Let rₙ = |ωₙ|. The counting function n(r) = #{n : rₙ ≤ r} satisfies n(r) ≤ C(1+r).

By Abel summation (or integral comparison), for α > 1:

$$\sum_{n=1}^{\infty}\frac{1}{(1+r_n)^{\alpha}} = \int_0^{\infty}\frac{1}{(1+r)^{\alpha}}\,dn(r)$$

where the integral is a Riemann-Stieltjes integral with respect to the counting measure dn(r).

Integrate by parts (Stieltjes):

$$\int_0^{\infty}\frac{1}{(1+r)^{\alpha}}\,dn(r) = \left[\frac{n(r)}{(1+r)^{\alpha}}\right]_0^{\infty} + \alpha\int_0^{\infty}\frac{n(r)}{(1+r)^{\alpha+1}}\,dr.$$

The boundary term: as r → ∞, n(r)/(1+r)^α ≤ C(1+r)/(1+r)^α = C(1+r)^{1-α} → 0 (since α > 1). At r = 0: n(0)/(1+0)^α = n(0), which is finite. So the boundary term vanishes.

The integral:

$$\alpha\int_0^{\infty}\frac{n(r)}{(1+r)^{\alpha+1}}\,dr \leq \alpha C\int_0^{\infty}\frac{1+r}{(1+r)^{\alpha+1}}\,dr = \alpha C\int_0^{\infty}\frac{1}{(1+r)^{\alpha}}\,dr.$$

Since α > 1:

$$\int_0^{\infty}\frac{dr}{(1+r)^{\alpha}} = \frac{1}{\alpha - 1} < \infty.$$

Therefore:

$$\sum_{n=1}^{\infty}\frac{1}{(1+|\omega_n|)^{\alpha}} \leq \frac{\alpha C}{\alpha - 1} < \infty. \qquad \blacksquare$$

## What Connects

**To the Hadamard factorization theorem.** An entire function of order ρ (here ρ ≤ 1, since |f| ≤ Be^{A|z|} is exponential type) has a canonical product representation with convergence exponent ≤ ρ. The convergence exponent is inf{α : Σ|ωₙ|^{-α} < ∞}. This problem proves the convergence exponent is ≤ 1, which is exactly what Hadamard's theorem needs for the Weierstrass product to use factors of genus ≤ 1.

**To Jensen's formula.** Jensen's formula is the bridge between function growth and zero distribution. It is the integral form of the argument principle, connecting the log-modulus average on circles to the counting function.

**To the Müntz-Szász theorem.** The convergence condition Σ 1/|ωₙ| = ∞ (divergence at α = 1) vs. convergence at α > 1 is the critical threshold. If the zeros are the reciprocals of a sequence {λₙ}, then Σ 1/λₙ diverging is the condition in the Müntz-Szász theorem for completeness of {x^{λₙ}} in C[0,1].

**To the exponent of convergence.** The result says the exponent of convergence of the zero sequence is at most 1. This is sharp: f(z) = sin(z) has zeros at nπ, and Σ|nπ|^{-α} converges iff α > 1. So the bound α > 1 cannot be improved to α > 1 - ε for functions of exponential type.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open Complex Filter Topology Set

noncomputable section

/-- An entire function of exponential type: |f(z)| ≤ B e^{A|z|}. -/
structure ExponentialType (f : ℂ → ℂ) : Prop where
  entire : Differentiable ℂ f
  A : ℝ
  B : ℝ
  hA : 0 < A
  hB : 0 < B
  bound : ∀ z, ‖f z‖ ≤ B * Real.exp (A * ‖z‖)

/-- The zero counting function: n(r) = number of zeros with |ω| ≤ r. -/
def zeroCount (f : ℂ → ℂ) (zeros : ℕ → ℂ) (r : ℝ) : ℕ :=
  (Finset.range (Nat.find (sorry))).card  -- conceptual; see below

/-- Jensen's formula: log|f(0)| + Σ log(R/|ωₙ|) = mean of log|f| on circle. -/
lemma jensen_formula
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    {R : ℝ} (hR : 0 < R)
    (ω : Fin n → ℂ) (hω : ∀ i, ‖ω i‖ < R)
    (hroots : ∀ z, ‖z‖ < R → f z = 0 ↔ ∃ i, z = ω i) :
    Real.log ‖f 0‖ + ∑ i, Real.log (R / ‖ω i‖) =
      (1 / (2 * Real.pi)) *
        ∮ z in C(0, R), Real.log ‖f z‖ := by
  sorry

/-- Step 1: The counting function grows at most linearly.
    n(r) ≤ C(1 + r) for all r > 0. -/
theorem counting_function_linear
    {f : ℂ → ℂ} (hf : ExponentialType f) (hf0 : f 0 ≠ 0)
    (ω : ℕ → ℂ) (hω_zeros : ∀ n, f (ω n) = 0)
    (hω_sorted : Monotone (fun n => ‖ω n‖)) :
    ∃ C > 0, ∀ r : ℝ, 0 < r →
      (Finset.filter (fun n => ‖ω n‖ ≤ r) (Finset.range (Nat.succ sorry))).card
        ≤ C * (1 + r) := by
  sorry

/-- Step 1, cleaner form: n(r) = O(r).
    Stated as: the set {n | ‖ω_n‖ ≤ r} has cardinality ≤ C(1+r). -/
lemma zero_count_le_linear
    {f : ℂ → ℂ} (hf : ExponentialType f) (hf0 : f 0 ≠ 0)
    (ω : ℕ → ℂ) (hω : ∀ n, f (ω n) = 0)
    (hω_all : ∀ z, f z = 0 → ∃ n, ω n = z) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (N : ℝ) ≤ C * (1 + ‖ω N‖) := by
  sorry

/-- Step 2: Abel summation converts counting function bound
    to series convergence.
    If n(r) ≤ C(1+r) then Σ (1+|ωₙ|)^{-α} < ∞ for α > 1. -/
lemma summable_of_counting_linear
    {ω : ℕ → ℂ} (hω_sorted : Monotone (fun n => ‖ω n‖))
    {C : ℝ} (hC : 0 < C)
    (h_count : ∀ N : ℕ, (N : ℝ) ≤ C * (1 + ‖ω N‖))
    {α : ℝ} (hα : 1 < α) :
    Summable (fun n => (1 + ‖ω n‖) ^ (-α)) := by
  sorry

/-- Comparison with p-series: if |ωₙ| grows at least linearly,
    then (1+|ωₙ|)^{-α} is dominated by n^{-α}. -/
lemma dominated_by_pseries
    {ω : ℕ → ℂ} (hω_sorted : Monotone (fun n => ‖ω n‖))
    {C : ℝ} (hC : 0 < C)
    (h_growth : ∀ N : ℕ, (N : ℝ) ≤ C * (1 + ‖ω N‖))
    {α : ℝ} (hα : 1 < α) :
    ∀ n : ℕ, (1 + ‖ω n‖) ^ (-α) ≤ C ^ α * (↑n + 1) ^ (-α) := by
  sorry

/-- Main theorem: Σ (1 + |ωₙ|)^{-α} < ∞ for all α > 1. -/
theorem zeros_summable_of_exponential_type
    {f : ℂ → ℂ} (hf : ExponentialType f)
    (ω : ℕ → ℂ)
    (hω_zeros : ∀ n, f (ω n) = 0)
    (hω_all : ∀ z, f z = 0 → ∃ n, ω n = z)
    (hω_sorted : Monotone (fun n => ‖ω n‖))
    {α : ℝ} (hα : 1 < α) :
    Summable (fun n => (1 + ‖ω n‖) ^ (-α)) := by
  sorry

/-- The convergence exponent of the zeros is at most 1. -/
theorem convergence_exponent_le_one
    {f : ℂ → ℂ} (hf : ExponentialType f)
    (ω : ℕ → ℂ)
    (hω_zeros : ∀ n, f (ω n) = 0)
    (hω_all : ∀ z, f z = 0 → ∃ n, ω n = z) :
    ∀ α : ℝ, 1 < α → Summable (fun n => ‖ω n‖ ^ (-α)) := by
  sorry

end
```

**Mathlib notes:**

- `ExponentialType` bundles entire + exponential growth bound. `Differentiable ℂ f` (without `On`) means entire.
- The zeros are given as a sequence `ω : ℕ → ℂ` sorted by modulus (`Monotone (fun n => ‖ω n‖)`), with `hω_zeros` (each ωₙ is a zero) and `hω_all` (every zero is listed).
- `Summable (fun n => (1 + ‖ω n‖) ^ (-α))` is the natural Mathlib encoding of Σ(1+|ωₙ|)^{-α} < ∞. The `rpow` with negative exponent gives (1+r)^{-α} = 1/(1+r)^α.
- The counting function bound is stated as `(N : ℝ) ≤ C * (1 + ‖ω N‖)` — since the zeros are sorted by modulus, this says the N-th zero has modulus ≥ N/C - 1, i.e., the zeros grow at least linearly. This is the dual form of "n(r) ≤ C(1+r)."
- `Real.rpow` handles the real power `(1 + ‖ω n‖) ^ (-α)`. Mathlib's `summable_rpow_inv` or comparison with p-series (`Real.summable_nat_rpow`) gives the convergence.
- Jensen's formula is not yet in Mathlib in packaged form, so `jensen_formula` is stated as a lemma. The circle integral `∮ z in C(0, R), ...` uses Mathlib's `circleIntegral`.
