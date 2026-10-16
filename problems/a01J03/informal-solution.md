

# APM a01J03: Differentiating a series of monotone functions term by term

## Why It's Hard

Swapping a derivative with an infinite sum is dangerous — it fails for general series of differentiable functions, even uniformly convergent ones. The standard sufficient conditions (uniform convergence of the derivatives, or domination by an integrable function) are not given here. What we *do* have is that each $f_n$ is nondecreasing and the sum converges pointwise. The difficulty is using monotonicity, not smoothness or uniform convergence, to justify the interchange. The proof must go through the theory of monotone functions (differentiable a.e., connection to measures) rather than through standard differentiation theorems.

## The Key Insight

Monotone functions are differentiable a.e. (Lebesgue's theorem), and the derivative can be computed via difference quotients. The key tool is the **monotone convergence theorem** applied to difference quotients — not the MCT for integrals, but the idea that nonneg terms can be summed and limited freely.

More precisely: the partial sums $S_{n}(x) = \sum_{k=1}^{N} f_k(x)$ are nondecreasing (finite sum of nondecreasing functions), so $S_N'$ exists a.e. and $S_N' = \sum_{k=1}^{N} f_k'$ a.e. (finite sum — no issue). The sequence $S_N'$ is nondecreasing (each added term $f_{N+1}' \geq 0$ a.e.) and $S_N' \leq f'$ a.e. (since $S_N \leq f$ and both are nondecreasing). The limit $\sum f_n' \leq f'$ a.e. is the easy direction. The hard direction — $f' \leq \sum f_n'$ a.e. — uses the fact that the "remainder" $f - S_N$ is also nondecreasing, so $(f - S_N)' \geq 0$ a.e., giving $f' \leq S_N' + (f - S_N)' \leq S_N' + (f - S_N)'$. We need $(f - S_N)' \to 0$ a.e., which requires a more careful argument via Lebesgue's differentiation theorem.

Actually, the cleanest proof goes through the **Lebesgue-Stieltjes measure** associated with each monotone function and uses the Radon-Nikodym theorem / MCT for measures.

## Complete Proof

**Theorem.** Let $f_n : \mathbb{R} \to [0,\infty)$ be nondecreasing for each $n$, and suppose $f(x) = \sum f_n(x) < \infty$ for all $x$. Then $f'(x) = \sum f_n'(x)$ for a.e. $x$.

**Proof.**

**Step 1: $f$ is nondecreasing.** If $x < y$, then $f_n(x) \leq f_n(y)$ for each $n$ (since each $f_n$ is nondecreasing), so $f(x) = \sum f_n(x) \leq \sum f_n(y) = f(y)$. ✓

**Step 2: All derivatives exist a.e.** By Lebesgue's theorem, every nondecreasing function on $\mathbb{R}$ is differentiable a.e. So $f'(x)$ and each $f_n'(x)$ exist for a.e. $x$, and $f'(x) \geq 0$, $f_n'(x) \geq 0$ a.e.

**Step 3: $\sum f_n'(x) \leq f'(x)$ a.e.**

Define the partial sums $S_N(x) = \sum_{n=1}^{N} f_n(x)$. Each $S_N$ is nondecreasing, and $S_N(x) \leq f(x)$ for all $x$. The difference quotient satisfies:

$$\frac{S_N(x+h) - S_N(x)}{h} = \sum_{n=1}^{N} \frac{f_n(x+h) - f_n(x)}{h} \leq \frac{f(x+h) - f(x)}{h}$$

for $h > 0$ (all terms nonneg, and $S_N \leq f$ implies $S_N(x+h) - S_N(x) \leq f(x+h) - f(x)$).

Taking $h \to 0$ at points where all derivatives exist (a.e.):

$$S_N'(x) = \sum_{n=1}^{N} f_n'(x) \leq f'(x).$$

Since this holds for all $N$, and all terms are nonneg:

$$\sum_{n=1}^{\infty} f_n'(x) \leq f'(x) \quad \text{a.e.}$$

**Step 4: $f'(x) \leq \sum f_n'(x)$ a.e., via integration.**

It suffices to show that for every compact interval $[a,b]$:

$$\int_a^b f'(x)\,dx \leq \int_a^b \sum_{n=1}^{\infty} f_n'(x)\,dx.$$

For a nondecreasing function $g$, Lebesgue's theorem gives $\int_a^b g'(x) dx \leq g(b) - g(a)$ (with equality iff $g$ is absolutely continuous; the inequality holds in general).

We have:

$$\int_a^b \sum_{n=1}^{\infty} f_n'(x)\,dx = \sum_{n=1}^{\infty}\int_a^b f_n'(x)\,dx$$

by the monotone convergence theorem (all terms nonneg).

Now:

$$\sum_{n=1}^{\infty}\int_a^b f_n'(x)\,dx \leq \sum_{n=1}^{\infty}(f_n(b) - f_n(a)) = f(b) - f(a).$$

(Using $\int f_n' \leq f_n(b) - f_n(a)$ for each nondecreasing $f_n$, and summing.)

But also, by the same inequality for $f$:

$$\int_a^b f'(x)\,dx \leq f(b) - f(a).$$

So both $\int f'$ and $\int \sum f_n'$ are $\leq f(b) - f(a)$. This doesn't directly compare them. We need a sharper argument.

**Step 4 (corrected): Use the inequality from Step 3 and the MCT.**

From Step 3, $\sum f_n'(x) \leq f'(x)$ a.e. Define $g(x) = f'(x) - \sum f_n'(x) \geq 0$ a.e. We want to show $g = 0$ a.e.

Define $R_N(x) = f(x) - S_N(x) = \sum_{n>N} f_n(x)$. Then $R_N$ is nondecreasing (sum of nondecreasing functions with nonneg values), and $R_N(x) \to 0$ for each $x$ (since $f(x) = \sum f_n(x)$ converges).

By Lebesgue's theorem, $R_N'$ exists a.e. and $R_N' \geq 0$. Also $f' = S_N' + R_N'$ a.e. (since $f = S_N + R_N$ and all are nondecreasing, their derivatives add; this is valid for finite sums of monotone functions). So:

$$g(x) = f'(x) - \sum_{n=1}^{\infty} f_n'(x) \leq f'(x) - S_N'(x) = R_N'(x) \quad \text{a.e.}$$

for every $N$. Now we show $\int_a^b R_N' dx \to 0$:

$$\int_a^b R_N'(x)\,dx \leq R_N(b) - R_N(a) = \sum_{n > N}(f_n(b) - f_n(a)).$$

Since $\sum_{n=1}^\infty (f_n(b) - f_n(a)) = f(b) - f(a) < \infty$, the tail $\sum_{n>N}(f_n(b) - f_n(a)) \to 0$ as $N \to \infty$.

So $\int_a^b R_N' dx \to 0$. Since $0 \leq g \leq R_N'$ a.e., we have $0 \leq \int_a^b g dx \leq \int_a^b R_N' dx \to 0$, so $\int_a^b g dx = 0$ for every $[a,b]$.

Since $g \geq 0$ a.e. and $\int_a^b g = 0$ for every interval, $g = 0$ a.e. on $\mathbb{R}$. ∎

## What Connects

**To the Fubini-Tonelli philosophy.** This is an interchange-of-limits theorem for nonneg terms. The monotone convergence theorem lets you interchange $\sum$ and $\int$ freely for nonneg functions. This problem is the differentiation analogue: interchange $\sum$ and $d/dx$ for nondecreasing functions.

**To Lebesgue's differentiation theorem.** The fact that a nondecreasing function is differentiable a.e. is essential. Without it, "$f'$" doesn't even make sense. The proof of Lebesgue's theorem uses the Vitali covering lemma, which is the deep ingredient underneath this problem.

**To the theory of monotone functions and measures.** Each nondecreasing $f_n$ defines a Lebesgue-Stieltjes measure $\mu_n$. The sum $f$ defines the measure $\mu = \sum \mu_n$. The derivatives $f_n'$ and $f'$ are the Radon-Nikodym derivatives $d\mu_n/dm$ and $d\mu/dm$. The result then follows from the countable additivity of Radon-Nikodym derivatives: $d(\sum \mu_n)/dm = \sum d\mu_n/dm$ a.e.

**To the Vitali-Carathéodory theorem.** The key inequality $\int g' \leq g(b) - g(a)$ for nondecreasing $g$ (with equality iff $g$ is absolutely continuous) is what makes the "remainder" argument work. The gap between $\int g'$ and $g(b) - g(a)$ is the singular part of the measure, which doesn't affect the a.e. derivative.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

open MeasureTheory Set Filter

noncomputable section

/-- Lebesgue's theorem: a monotone function is differentiable a.e. -/
lemma monotone_differentiableAE
    {g : ℝ → ℝ} (hg : Monotone g) :
    ∀ᵐ x ∂volume, DifferentiableAt ℝ g x := by
  sorry

/-- The derivative of a nondecreasing function is nonneg a.e. -/
lemma monotone_deriv_nonneg
    {g : ℝ → ℝ} (hg : Monotone g) :
    ∀ᵐ x ∂volume, 0 ≤ deriv g x := by
  sorry

/-- Lebesgue's inequality: ∫_a^b g' ≤ g(b) - g(a) for nondecreasing g. -/
lemma monotone_integral_deriv_le
    {g : ℝ → ℝ} (hg : Monotone g)
    {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Icc a b, deriv g x ∂volume ≤ g b - g a := by
  sorry

/-- A finite sum of nondecreasing functions is nondecreasing. -/
lemma monotone_sum {f : ℕ → ℝ → ℝ} (hf : ∀ n, Monotone (f n)) (N : ℕ) :
    Monotone (fun x => ∑ n in Finset.range N, f n x) := by
  sorry

/-- The pointwise sum of nondecreasing nonneg functions is nondecreasing. -/
lemma monotone_tsum
    {f : ℕ → ℝ → ℝ} (hf : ∀ n, Monotone (f n))
    (hnn : ∀ n x, 0 ≤ f n x)
    (hconv : ∀ x, Summable (fun n => f n x)) :
    Monotone (fun x => ∑' n, f n x) := by
  sorry

/-- The easy direction: Σ f_n'(x) ≤ f'(x) a.e.
    From the partial sum bound S_N ≤ f and taking derivatives. -/
lemma tsum_deriv_le_deriv_tsum
    {f : ℕ → ℝ → ℝ} (hf : ∀ n, Monotone (f n))
    (hnn : ∀ n x, 0 ≤ f n x)
    (hconv : ∀ x, Summable (fun n => f n x)) :
    ∀ᵐ x ∂volume,
      ∑' n, deriv (f n) x ≤ deriv (fun x => ∑' n, f n x) x := by
  sorry

/-- The remainder R_N = f - S_N is nondecreasing and R_N(x) → 0. -/
lemma remainder_monotone_tendsto
    {f : ℕ → ℝ → ℝ} (hf : ∀ n, Monotone (f n))
    (hnn : ∀ n x, 0 ≤ f n x)
    (hconv : ∀ x, Summable (fun n => f n x)) (x : ℝ) :
    Tendsto (fun N => (∑' n, f n x) - ∑ n in Finset.range N, f n x)
      atTop (𝓝 0) := by
  sorry

/-- The tail integral vanishes: ∫_a^b R_N' → 0. -/
lemma remainder_integral_deriv_tendsto
    {f : ℕ → ℝ → ℝ} (hf : ∀ n, Monotone (f n))
    (hnn : ∀ n x, 0 ≤ f n x)
    (hconv : ∀ x, Summable (fun n => f n x))
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun N => ∫ x in Icc a b,
      deriv (fun x => (∑' n, f n x) - ∑ n in Finset.range N, f n x) x ∂volume)
      atTop (𝓝 0) := by
  sorry

/-- Main theorem: f'(x) = Σ f_n'(x) a.e.
    Differentiation and summation commute for series of nondecreasing
    nonneg functions with pointwise-finite sum. -/
theorem deriv_tsum_eq_tsum_deriv
    {f : ℕ → ℝ → ℝ} (hf : ∀ n, Monotone (f n))
    (hnn : ∀ n x, 0 ≤ f n x)
    (hconv : ∀ x, Summable (fun n => f n x)) :
    ∀ᵐ x ∂volume,
      deriv (fun x => ∑' n, f n x) x = ∑' n, deriv (f n) x := by
  sorry

end
```

**Mathlib notes:**

- `Monotone g` says $g$ is nondecreasing ($\forall x y, x \leq y \to g x \leq g y$). This is the standard Mathlib predicate.
- `deriv g x` is the derivative; `DifferentiableAt ℝ g x` says it exists. Lebesgue's theorem (`monotone_differentiableAE`) guarantees existence a.e. for monotone functions — this is a deep result not yet fully in Mathlib.
- `∑' n, f n x` is the infinite sum `tsum` — it equals the series when `Summable` and 0 otherwise.
- `∀ᵐ x ∂volume, P x` is `∀ᶠ x in ae volume, P x`, the standard "for a.e. $x$" predicate.
- The proof structure is: `tsum_deriv_le_deriv_tsum` (easy direction via partial sums) + `remainder_integral_deriv_tendsto` (tail integral $\to 0$) + squeeze to get equality a.e.
- The Lebesgue-Stieltjes measure approach (mentioned in "What Connects") would use `StieltjesFunction` and `MeasureTheory.Measure.StieltjesFunction.measure` from Mathlib, with the Radon-Nikodym derivative giving $f'$. This is an alternative formalization route.
