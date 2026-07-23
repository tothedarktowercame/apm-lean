

# APM a01J04: Taylor coefficients at z=2 recover the residue at z=1

## Why It's Hard

The Taylor coefficients f⁽ⁿ⁾(2)/n! live at z = 2, while the residue λ lives at z = 1. The problem asks you to show these are related with superexponential precision: the error decays faster than any exponential T⁻ⁿ. This is surprising because the Taylor series at z = 2 has radius of convergence exactly 1 (the nearest singularity is z = 1, at distance 1 from z = 2), so the coefficients behave like 1ⁿ = 1 in magnitude. The claim is that the *specific* part of the coefficients coming from the pole at z = 1 dominates, with everything else decaying superexponentially.

## The Key Insight

Decompose f(z) = λ/(z-1) + g(z), where g is entire (analytic on all of ℂ, since the pole was simple and we've subtracted it). The Taylor coefficients of λ/(z-1) at z = 2 are exactly (-1)ⁿ λ (from the geometric series). The Taylor coefficients of g at z = 2 are g⁽ⁿ⁾(2)/n!, and since g is entire, these decay faster than any R⁻ⁿ by the Cauchy estimates. The combination gives the result.

## Complete Proof

**Theorem.** Let f be analytic on ℂ \ {1} with a simple pole at z = 1 with residue λ. Then for all T > 0:

$$\lim_{n \to \infty} T^n \left|(-1)^n \frac{f^{(n)}(2)}{n!} - \lambda\right| = 0.$$

**Proof.**

**Step 1: Decompose f.** Since f has a simple pole at z = 1 with residue λ, the function

$$g(z) = f(z) - \frac{\lambda}{z - 1}$$

is analytic on ℂ \ {1} and has a removable singularity at z = 1 (the pole has been subtracted). Defining g(1) by continuity, g becomes an **entire function**.

**Step 2: Taylor coefficients of λ/(z-1) at z = 2.** Write:

$$\frac{\lambda}{z - 1} = \frac{\lambda}{1 + (z - 2)} = \lambda \sum_{n=0}^{\infty} (-1)^n (z-2)^n, \quad |z-2| < 1.$$

So the n-th Taylor coefficient of λ/(z-1) at z = 2 is (-1)ⁿ λ. Equivalently, the n-th derivative at z = 2 of λ/(z-1) is:

$$\frac{d^n}{dz^n}\left[\frac{\lambda}{z-1}\right]\bigg|_{z=2} = \lambda \cdot (-1)^n \cdot n!$$

so the coefficient is (-1)ⁿ λ. ✓

**Step 3: Taylor coefficients of g at z = 2.** Since g is entire, g is analytic on every disk D(2, R) for every R > 0. By the Cauchy estimates:

$$\left|\frac{g^{(n)}(2)}{n!}\right| \leq \frac{\max_{|z-2|=R} |g(z)|}{R^n} = \frac{M(R)}{R^n}$$

where M(R) = max\_{|z-2|=R} |g(z)| is finite for each R.

**Step 4: Combine.** Since f = λ/(z-1) + g:

$$\frac{f^{(n)}(2)}{n!} = (-1)^n \lambda + \frac{g^{(n)}(2)}{n!}.$$

Therefore:

$$(-1)^n \frac{f^{(n)}(2)}{n!} - \lambda = (-1)^n \cdot \frac{g^{(n)}(2)}{n!}.$$

Wait — let me recompute. We have:

$$\frac{f^{(n)}(2)}{n!} = \frac{(-1)^n \lambda \cdot n!}{n!} + \frac{g^{(n)}(2)}{n!} = (-1)^n \lambda + \frac{g^{(n)}(2)}{n!}.$$

So:

$$(-1)^n \frac{f^{(n)}(2)}{n!} - \lambda = (-1)^n\left[(-1)^n \lambda + \frac{g^{(n)}(2)}{n!}\right] - \lambda = \lambda + (-1)^n\frac{g^{(n)}(2)}{n!} - \lambda = (-1)^n \frac{g^{(n)}(2)}{n!}.$$

Therefore:

$$T^n\left|(-1)^n \frac{f^{(n)}(2)}{n!} - \lambda\right| = T^n \left|\frac{g^{(n)}(2)}{n!}\right| \leq T^n \cdot \frac{M(R)}{R^n} = M(R) \cdot \left(\frac{T}{R}\right)^n.$$

For any T > 0, choose R = 2T (or any R > T). Then T/R = 1/2 < 1, so:

$$T^n \left|(-1)^n \frac{f^{(n)}(2)}{n!} - \lambda\right| \leq M(2T) \cdot 2^{-n} \to 0.$$

Since T was arbitrary, this completes the proof. ∎

## What Connects

**To the Laurent/Taylor coefficient relationship.** The residue at a pole determines the "leading term" of the Taylor expansion at any nearby regular point. The remaining (entire) part contributes coefficients that decay faster than any geometric rate — this is precisely the characterisation of entire functions by their Taylor coefficients.

**To the Darboux/transfer method.** In analytic combinatorics, the asymptotic behaviour of Taylor coefficients [zⁿ]f(z) is governed by the singularity nearest to the expansion point. Here the singularity at z = 1 (distance 1 from z = 2) determines the leading asymptotics (-1)ⁿ λ, and the error is exponentially small because the next singularity is infinitely far away (g is entire).

**To the Cauchy estimates.** The Cauchy bound |g⁽ⁿ⁾(a)/n!| ≤ M(R)/Rⁿ for entire g is the reason that entire functions have Taylor coefficients decaying faster than any geometric series. This is equivalent to the radius of convergence being infinite.

**To the uniqueness of the residue.** The result shows that the residue λ is recoverable from the Taylor coefficients at z = 2 via (-1)ⁿ f⁽ⁿ⁾(2)/n! → λ. In fact the convergence is superexponentially fast. This is a concrete instance of the general principle that local singularity data can be read off from Taylor data at a remote point, up to exponentially small errors.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Order.Filter.Basic

open Complex Filter Topology Metric

noncomputable section

/-- f has a simple pole at z = 1 with residue λ:
    f(z) - λ/(z-1) extends to an entire function. -/
structure HasSimplePole (f : ℂ → ℂ) (λ' : ℂ) : Prop where
  analytic_off_pole : DifferentiableOn ℂ f {(1 : ℂ)}ᶜ
  removable : Differentiable ℂ (fun z => f z - λ' / (z - 1))

/-- The entire part: g = f - λ/(z-1) is entire. -/
def entirePart (f : ℂ → ℂ) (λ' : ℂ) : ℂ → ℂ :=
  fun z => f z - λ' / (z - 1)

/-- Cauchy estimate: Taylor coefficients of an entire function
    at any point decay faster than any R⁻ⁿ. -/
lemma entire_taylor_coeff_superexp_decay
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (a : ℂ)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => T ^ n * ‖iteratedDeriv n g a / n !‖)
      atTop (𝓝 0) := by
  sorry

/-- The Cauchy bound for entire functions:
    |g^{(n)}(a)/n!| ≤ M(R)/R^n for any R > 0. -/
lemma entire_cauchy_bound
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (a : ℂ)
    {R : ℝ} (hR : 0 < R) :
    ‖iteratedDeriv n g a / n !‖ ≤
      (⨆ w ∈ sphere a R, ‖g w‖) / R ^ n := by
  sorry

/-- Taylor coefficients of λ/(z-1) at z = 2:
    the n-th coefficient is (-1)^n λ. -/
lemma pole_taylor_coeff_at_two (λ' : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => λ' / (z - 1)) 2 / n ! =
      (-1) ^ n * λ' := by
  sorry

/-- The error after subtracting the pole contribution
    equals the Taylor coefficients of the entire part. -/
lemma error_eq_entire_coeff
    {f : ℂ → ℂ} {λ' : ℂ} (hf : HasSimplePole f λ')
    (n : ℕ) :
    (-1) ^ n * (iteratedDeriv n f 2 / n !) - λ' =
      (-1) ^ n * (iteratedDeriv n (entirePart f λ') 2 / n !) := by
  sorry

/-- Main theorem: T^n |(-1)^n f^{(n)}(2)/n! - λ| → 0 for all T > 0.
    The residue is recovered from the Taylor coefficients at z = 2
    with superexponential precision. -/
theorem residue_from_taylor_coefficients
    {f : ℂ → ℂ} {λ' : ℂ} (hf : HasSimplePole f λ')
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => T ^ n *
      ‖(-1) ^ n * (iteratedDeriv n f 2 / ↑(n !)) - λ'‖)
      atTop (𝓝 0) := by
  sorry

/-- Corollary: (-1)^n f^{(n)}(2)/n! → λ (without the T^n factor). -/
theorem taylor_coeffs_converge_to_residue
    {f : ℂ → ℂ} {λ' : ℂ} (hf : HasSimplePole f λ') :
    Tendsto (fun n => (-1) ^ n * (iteratedDeriv n f 2 / ↑(n !)))
      atTop (𝓝 λ') := by
  sorry

end
```

**Mathlib notes:**

- `iteratedDeriv n f z` is the n-th derivative of f at z. `iteratedDeriv n f z / n !` gives the n-th Taylor coefficient.
- `HasSimplePole` bundles the hypotheses: f is analytic on ℂ \ {1}, and f(z) - λ/(z-1) extends to an entire function. The `Differentiable ℂ` predicate (without `On`) means entire.
- `(-1) ^ n` for `n : ℕ` gives `1` or `-1` in ℂ as needed. The coercion `↑(n !)` converts `ℕ` factorial to ℂ.
- The Cauchy bound `entire_cauchy_bound` uses `⨆ w ∈ sphere a R, ‖g w‖` for the supremum of |g| on the circle. Mathlib has `Complex.norm_iteratedDeriv_le_of_differentiableOn` for related bounds.
- The proof chain: `error_eq_entire_coeff` reduces the error to Taylor coefficients of g (entire), then `entire_taylor_coeff_superexp_decay` gives T^n · |coeff| → 0 for any T.
- `Tendsto ... atTop (𝓝 0)` encodes the limit statement with `T^n` factor.
