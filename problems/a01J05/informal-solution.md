

# APM a01J05: Zeros of the derivative of a finite Blaschke-type function

## Why It's Hard

The hypothesis — |f| = 1 on the unit circle, f analytic on a neighbourhood of the closed disk, N zeros inside — pins down f as a finite Blaschke product (up to a constant of modulus 1). The conclusion that f' has exactly N-1 zeros inside the disk is a complex-analytic analogue of "a degree-N polynomial has N-1 critical points." But f is not a polynomial — it's a rational function of a specific form — and the proof must use the argument principle or the structure of Blaschke products, not just degree counting.

## The Key Insight

**f is a finite Blaschke product.** The conditions (analytic on a neighbourhood of the closed disk, |f| = 1 on the unit circle, N zeros inside) force f(z) = e^{iθ} ∏\_{k=1}^{N} (z - aₖ)/(1 - ā\_k z) for some |aₖ| < 1. This is a rational function of degree N, and the number of zeros of f' inside the disk is computed by the argument principle applied to f'/f = (log f)'.

Alternatively, **use the argument principle directly**: the number of zeros of f' inside the disk is (1/2πi) ∮\_{|z|=1} f''/f' dz. Compute this using the logarithmic derivative.

## Complete Proof

**Theorem.** Let f be analytic on an open set containing the closed unit disk, with |f(z)| = 1 for |z| = 1 and exactly N zeros (counted with multiplicity) in the open unit disk. Then f' has exactly N - 1 zeros (counted with multiplicity) in the open unit disk.

**Proof.**

**Step 1: f is a finite Blaschke product.**

Let a₁, ..., a\_N be the zeros of f in the open disk (with multiplicity). The function

$$B(z) = e^{i\theta}\prod_{k=1}^{N}\frac{z - a_k}{1 - \bar{a}_k z}$$

is a Blaschke product of degree N. It has the same zeros as f in the disk, and |B(z)| = 1 for |z| = 1.

Consider h(z) = f(z)/B(z). Then h is analytic on a neighbourhood of the closed disk (the denominator factors 1 - ā\_k z are nonzero for |z| ≤ 1 since |a\_k| < 1), h has no zeros in the closed disk (the zeros of f are cancelled by B), and |h(z)| = |f(z)|/|B(z)| = 1/1 = 1 for |z| = 1.

By the maximum modulus principle applied to h and 1/h on the closed disk: |h(z)| ≤ 1 and |1/h(z)| ≤ 1 for |z| ≤ 1, so |h(z)| = 1 for all |z| ≤ 1. By the open mapping theorem (or maximum modulus), h is constant: h(z) = c with |c| = 1.

So f(z) = c · B(z) is indeed a finite Blaschke product of degree N (absorbing c into the phase e^{iθ}). ✓

**Step 2: Count zeros of f' via the argument principle.**

Since f is analytic and nonvanishing on the unit circle (|f| = 1 there), and f' is analytic on a neighbourhood of the closed disk, the number of zeros of f' inside the disk (counted with multiplicity) is:

$$Z_{f'} = \frac{1}{2\pi i}\oint_{|z|=1}\frac{f''(z)}{f'(z)}\,dz.$$

We compute this differently. Consider the logarithmic derivative:

$$\frac{f'(z)}{f(z)} = \frac{d}{dz}\log f(z).$$

The number of zeros of f inside the disk is:

$$N = \frac{1}{2\pi i}\oint_{|z|=1}\frac{f'(z)}{f(z)}\,dz.$$

This is the winding number of f around 0 as z traverses the unit circle, i.e., the degree of the map f : S¹ → S¹. Since f is a Blaschke product of degree N, this winding number is N. ✓

**Step 3: Compute the winding number of f' directly.**

Since |f(z)| = 1 on the unit circle, we can write f(z) = e^{iφ(z)} for z on the circle, where φ is a real-valued function. Then f'(z) = iφ'(z) f(z) on the circle. Since |f| = 1 on the circle, f' has zeros on the circle only where φ'(z) = 0.

But we need a different approach. Let's use the fact that f maps the unit circle to itself with degree N (winding number N). This means f' has exactly N-1 zeros inside by the following argument.

**Step 4: Direct count via the Blaschke product.**

Write f(z) = e^{iθ} ∏\_{k=1}^{N} (z - aₖ)/(1 - ā\_k z). The logarithmic derivative is:

$$\frac{f'(z)}{f(z)} = \sum_{k=1}^{N}\frac{1}{z - a_k} + \sum_{k=1}^{N}\frac{\bar{a}_k}{1 - \bar{a}_k z}.$$

The function f'/f is meromorphic on the closed disk with simple poles at a₁, ..., a\_N (the zeros of f) inside the disk. It has no poles on the circle (since f ≠ 0 there) and no poles from the 1/(1 - ā\_k z) terms (since |a\_k| < 1 means 1/ā\_k is outside the disk).

The number of zeros of f' inside the disk equals the number of zeros of f'/f inside the disk plus the number of poles of f'/f inside the disk (since zeros of f' = zeros of (f'/f · f) = zeros of f'/f + zeros of f, minus cancellations... this is getting complicated).

**Step 5: Cleaner argument using the argument principle for f'.**

f is a rational function of degree N (a Blaschke product), so f can be written as P(z)/Q(z) where P has degree N and Q has degree N (with Q(z) = ∏(1 - ā\_k z)). Then:

$$f'(z) = \frac{P'(z)Q(z) - P(z)Q'(z)}{Q(z)^2}.$$

The numerator P'Q - PQ' is a polynomial. deg(P'Q) = (N-1) + N = 2N-1. deg(PQ') = N + (N-1) = 2N-1. So the numerator has degree at most 2N - 1.

The zeros of f' are the zeros of P'Q - PQ' that are not zeros of Q² (i.e., not at the points 1/ā\_k, which are outside the disk). So f' has at most 2N - 1 zeros total (on ℂ).

Now count the zeros of f' **outside** the closed disk and **on** the circle.

**Zeros on the circle:** f has no zeros on the circle, so f' can have zeros on the circle only where the argument of f is stationary. But for a Blaschke product of degree N ≥ 1, the map f : S¹ → S¹ has degree N, so arg f increases by 2πN as z goes around the circle. The derivative of the argument is strictly positive (for the standard Blaschke product, this can be verified directly), so f' ≠ 0 on the circle. Let me verify: on |z| = 1, z = e^{iθ}:

$$\frac{d}{d\theta}f(e^{i\theta}) = ie^{i\theta}f'(e^{i\theta}).$$

Since |f| = 1 on the circle, |df/dθ| = |f'(e^{iθ})| (with the ie^{iθ} factor having modulus 1). The derivative of the argument of f is Im(f'/f · iz) = Re(iz f'/f). For a Blaschke product:

$$izf'(z)/f(z) = iz\sum_k\left(\frac{1}{z-a_k}+\frac{\bar{a}_k}{1-\bar{a}_kz}\right).$$

For |z| = 1, one computes that this equals Σ\_k (1 - |a\_k|²)/|z - a\_k|² > 0. So the argument is strictly increasing, meaning f' ≠ 0 on the unit circle. ✓

**Zeros outside the disk:** By the reflection principle / symmetry of Blaschke products: if w₀ is a zero of f' with |w₀| > 1, then 1/w̄₀ is also a zero of f' with |1/w̄₀| < 1 (this follows from the identity f(z) = 1/f̄(1/z̄) for Blaschke products). So the zeros of f' outside the disk are in bijection with some zeros inside (paired by z ↔ 1/z̄).

Let Z\_in = number of zeros of f' with |z| < 1, Z\_out = number with |z| > 1. The reflection symmetry gives Z\_in = Z\_out. The total number of zeros of f' (counting the denominator's contribution) equals 2N - 1 (the degree of the numerator P'Q - PQ'). But f' also has poles at the zeros of Q² that are outside the disk (2N poles at 1/ā\_k, counted with multiplicity). Wait, let me reconsider.

Actually f'(z) = (P'Q - PQ')/Q². As a rational function, f' has 2N-1 zeros and 2N poles (at the N points 1/ā\_k, each of order 2). The number of zeros minus poles of f' on ℂ (including ∞) must equal zero (for a rational function, the degree of the numerator equals the degree of the denominator modulo the degree at ∞).

Actually, for a rational function R = p/q in lowest terms, the number of zeros equals the number of poles (each counted with multiplicity, including at ∞). Here f' = (P'Q - PQ')/Q², which may not be in lowest terms if P and Q share common factors — but for a Blaschke product with distinct zeros, they don't.

**Cleaner approach using the argument principle directly.**

Apply the argument principle to f':

$$Z_{f'} - P_{f'} = \frac{1}{2\pi i}\oint_{|z|=1}\frac{f''(z)}{f'(z)}\,dz$$

where Z\_{f'} = zeros of f' and P\_{f'} = poles of f' inside the disk. Since f is analytic on a neighbourhood of the closed disk, f' has no poles inside the disk, so P\_{f'} = 0.

The integral (1/2πi) ∮ f''/f' dz is the winding number of f'(z) as z traverses the unit circle. Since f' ≠ 0 on the circle (Step 5 above), this winding number is well-defined.

On the unit circle, f(z) maps the circle to itself with winding number N. The derivative f'(z) = (d/dz)f(z) can be related to the tangential derivative: df/dθ = iz f'(z). Since f maps the circle to itself with winding number N, the tangential derivative df/dθ maps the circle to a curve that winds N-1 times around the origin. (This is because the tangent vector to a degree-N map of the circle has winding number N-1: the Gauss map of a degree-N curve has degree N-1.)

More precisely: on the circle, f(e^{iθ}) = e^{iψ(θ)} where ψ(2π) - ψ(0) = 2πN. The tangential derivative is ie^{iθ}f'(e^{iθ}) = iψ'(θ)e^{iψ(θ)}. The winding number of this as θ goes from 0 to 2π is the winding number of ψ'(θ) · e^{iψ(θ)}. Since ψ' > 0 (proved above), the winding number of ψ'(θ)e^{iψ(θ)} equals 0 + N = N (the real positive factor ψ' doesn't contribute to the winding, and e^{iψ} winds N times).

So the winding number of ie^{iθ}f'(e^{iθ}) around the origin is N. Since ie^{iθ} has winding number 1, the winding number of f'(e^{iθ}) is N - 1.

Therefore:

$$Z_{f'} = \frac{1}{2\pi i}\oint_{|z|=1}\frac{f''}{f'}\,dz = N - 1. \qquad \blacksquare$$

## What Connects

**To finite Blaschke products.** The condition "|f| = 1 on the unit circle, f analytic, N zeros inside" uniquely characterises finite Blaschke products (up to a unimodular constant). This problem is really about Blaschke products.

**To the Gauss-Lucas theorem.** For polynomials, the zeros of p' lie in the convex hull of the zeros of p. This problem is the unit-disk analogue: for Blaschke products, the critical points of f lie inside the unit disk (and there are exactly N-1 of them).

**To the Argument Principle.** The winding number computation (Step 5) is the argument principle applied to f'. The key subtlety is computing the winding number of f' on the circle from the degree of f, which requires the tangential derivative computation.

**To the degree of a map.** The result is fundamentally topological: a degree-N holomorphic self-map of the disk has exactly N-1 critical points (counted with multiplicity). The Riemann-Hurwitz formula generalises this to maps between Riemann surfaces.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.Connected.Basic

open Complex Metric Set Filter Polynomial

noncomputable section

/-- A function satisfying the hypotheses: analytic near the closed disk,
    |f| = 1 on the boundary, N zeros inside. -/
structure BlaschkeData (f : ℂ → ℂ) (N : ℕ) : Prop where
  analytic : DifferentiableOn ℂ f (closedBall 0 1)
  analytic_nhd : ∃ ε > 0, DifferentiableOn ℂ f (closedBall 0 (1 + ε))
  boundary_unit : ∀ z, ‖z‖ = 1 → ‖f z‖ = 1
  zeros_count : ∃ (a : Fin N → ℂ),
    (∀ i, ‖a i‖ < 1) ∧
    (∀ z, ‖z‖ < 1 → f z = 0 ↔ ∃ i, z = a i)

/-- f is a finite Blaschke product: follows from the hypotheses
    by the maximum modulus principle applied to f/B and B/f. -/
lemma is_blaschke_product {f : ℂ → ℂ} {N : ℕ}
    (hf : BlaschkeData f N) :
    ∃ (θ : ℝ) (a : Fin N → ℂ),
      (∀ i, ‖a i‖ < 1) ∧
      ∀ z, ‖z‖ < 1 + ε → f z = exp (I * θ) *
        ∏ i, (z - a i) / (1 - conj (a i) * z) := by
  sorry

/-- f' has no zeros on the unit circle when f is a Blaschke product
    of degree N ≥ 1. The argument derivative is strictly positive. -/
lemma deriv_ne_zero_on_circle {f : ℂ → ℂ} {N : ℕ}
    (hf : BlaschkeData f N) (hN : 0 < N) :
    ∀ z, ‖z‖ = 1 → deriv f z ≠ 0 := by
  sorry

/-- The argument derivative is strictly positive:
    Re(iz f'(z)/f(z)) > 0 on |z| = 1.
    This equals Σ (1 - |aₖ|²)/|z - aₖ|². -/
lemma arg_deriv_pos {f : ℂ → ℂ} {N : ℕ}
    (hf : BlaschkeData f N) (hN : 0 < N) :
    ∀ z, ‖z‖ = 1 →
      0 < (I * z * deriv f z / f z).re := by
  sorry

/-- The winding number of f on the unit circle equals N
    (= number of zeros, by the argument principle). -/
lemma winding_number_f_eq_N {f : ℂ → ℂ} {N : ℕ}
    (hf : BlaschkeData f N) :
    (1 / (2 * π * I)) * ∮ z in C(0, 1), deriv f z / f z = N := by
  sorry

/-- The winding number of f' on the unit circle equals N - 1.
    From the tangential derivative: f'(eⁱᶿ) has winding N - 1
    because the factor ieⁱᶿ contributes +1 to the winding of
    ieⁱᶿf'(eⁱᶿ), which has winding N. -/
lemma winding_number_deriv_eq {f : ℂ → ℂ} {N : ℕ}
    (hf : BlaschkeData f N) (hN : 0 < N) :
    (1 / (2 * π * I)) *
      ∮ z in C(0, 1), iteratedDeriv 2 f z / deriv f z = ↑N - 1 := by
  sorry

/-- Main theorem: f' has exactly N - 1 zeros inside the unit disk,
    counted with multiplicity. -/
theorem blaschke_deriv_zeros {f : ℂ → ℂ} {N : ℕ}
    (hf : BlaschkeData f N) (hN : 0 < N) :
    ∃ (b : Fin (N - 1) → ℂ),
      (∀ j, ‖b j‖ < 1) ∧
      ∀ z, ‖z‖ < 1 → deriv f z = 0 ↔ ∃ j, z = b j := by
  sorry

/-- Alternative statement using the argument principle integral
    to count zeros of f'. -/
theorem blaschke_deriv_zero_count {f : ℂ → ℂ} {N : ℕ}
    (hf : BlaschkeData f N) (hN : 0 < N) :
    (1 / (2 * π * I)) *
      ∮ z in C(0, 1), iteratedDeriv 2 f z / deriv f z = ↑(N - 1) := by
  sorry

end
```

**Mathlib notes:**

- `BlaschkeData` bundles all hypotheses: analyticity on a neighbourhood of the closed disk, |f| = 1 on the boundary, and N zeros inside. The zeros are given as a `Fin N`-indexed family for the multiplicity count.
- `∮ z in C(0, 1), g z` denotes the contour integral over the unit circle — in Mathlib this would use `circleIntegral` from `Mathlib.Analysis.Complex.CauchyIntegral`.
- `iteratedDeriv 2 f z` is f''(z); the ratio `f''/f'` is the logarithmic derivative of f'.
- The main theorem `blaschke_deriv_zeros` states the existence of exactly N-1 zeros of f' inside the disk, parameterised by `Fin (N-1)`.
- The proof chain: `is_blaschke_product` (structure theorem) → `arg_deriv_pos` (f' ≠ 0 on circle) → `winding_number_deriv_eq` (winding number computation) → `blaschke_deriv_zeros` (argument principle).
- The winding number computation is the core: the tangential derivative `ie^{iθ}f'(e^{iθ})` has winding N (from the degree-N map), and subtracting the winding of `ie^{iθ}` (which is 1) gives N-1 for f'.
