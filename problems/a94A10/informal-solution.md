

# APM a94A10: $f$ real iff $z$ real implies $f'$ never vanishes on $\mathbb{R}$

## 1. Informal proof

**Why it's hard.** The hypothesis "$f(z)$ is real $\Longleftrightarrow$ $z$ is real" is a topological condition on the preimage of $\mathbb{R}$ under $f$, and connecting it to the non-vanishing of $f'$ requires understanding how holomorphic maps behave near points where the derivative vanishes (they are locally $n$-to-1, which would create non-real points mapping to real values).

**The key insight.** If $f'(x_{0}) = 0$ at some real $x_{0}$, then $f$ has a critical point: locally $f(z) \approx f(x_{0}) + c(z-x_{0})^{n}$ for some $n \geq 2$. This $n$-to-1 local map sends $n$ distinct branches near $x_{0}$ to the same real value. Since $n \geq 2$, at least one branch goes into the upper half-plane while mapping to a real value — contradicting "$f(z)$ real $\Longrightarrow$ $z$ real."

**Proof.**

Suppose for contradiction that $f'(x_{0}) = 0$ for some $x_{0} \in \mathbb{R}$. Since $f$ is entire and nonconstant (a constant function has $f(z)$ real for all $z$, violating "$f(z)$ real $\Longrightarrow$ $z$ real" unless the domain is restricted), $f$ has a zero of order $n \geq 2$ at $x_{0}$ for $g(z) := f(z) - f(x_{0})$. So:

$g(z) = a_{n}(z - x_{0})^{n} + a_{n+1}(z - x_{0})^{n+1} + \cdots$

with $a_{n} \neq 0$ and $n \geq 2$.

Since $f$ maps $\mathbb{R}$ to $\mathbb{R}$ (the forward direction of the hypothesis), $f$ has real coefficients in its Taylor expansion at $x_{0}$ (by the Schwarz reflection principle, or directly: $f^{(k)}(x_{0}) \in \mathbb{R}$ for all $k$ since $f$ is real-valued on $\mathbb{R}$). So $a_{n} \in \mathbb{R}$, $a_{n} \neq 0$.

The local mapping behaviour near $x_{0}$: $g(z) = a_{n}(z-x_{0})^{n}(1 + h(z))$ where $h(z) \to 0$, so $g$ is locally an $n$-fold covering. Specifically, for small $w$ near 0, the equation $g(z) = w$ has exactly $n$ solutions near $x_{0}$.

Now consider small real values $w > 0$ (or $w < 0$, choosing the sign so that $w/a_{n} > 0$). The equation $g(z) = w$ near $x_{0}$ has $n$ solutions, which are approximately the $n$-th roots of $w/a_{n}$:

$z - x_{0} \approx (w/a_{n})^{1/n} \cdot e^{2\pi ik/n}$, $k = 0, 1, \ldots, n-1$.

Since $w/a_{n} > 0$, the $n$-th roots include $(w/a_{n})^{1/n} \cdot e^{2\pi i/n}$ for $k = 1$, which is not real (since $n \geq 2$ and $2\pi/n \in (0, \pi)$). This gives a non-real $z$ with $g(z) = w$, hence $f(z) = f(x_{0}) + w \in \mathbb{R}$. But $z \notin \mathbb{R}$ — contradicting "$f(z)$ real $\Longrightarrow$ $z$ real." ∎

**What connects.** This is fundamentally about the local mapping theorem for holomorphic functions: near a critical point of order $n$, $f$ is locally $n$-to-1, acting like $z \mapsto z^{n}$. The hypothesis that $f^{-1}(\mathbb{R}) = \mathbb{R}$ is a very strong topological constraint — it says the preimage of a line is a line. A holomorphic map that is locally $n$-to-1 ($n \geq 2$) cannot preserve this linear structure because the $n$-fold branching sends multiple directions (including non-real ones) to the same real target. The result connects to the open mapping theorem ($f$ is open, so $f^{-1}(\mathbb{R})$ being a real-analytic curve imposes rigidity), the Schwarz reflection principle ($f$ has real coefficients), and the theory of branched coverings.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex

noncomputable section

/-- The "real iff real" hypothesis. -/
def RealIffReal (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, (f z).im = 0 ↔ z.im = 0

/-- Main theorem: f'(x) ≠ 0 for all real x. -/
theorem deriv_ne_zero_on_reals
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hreal : RealIffReal f) :
    ∀ x : ℝ, deriv f (↑x) ≠ 0 := by
  sorry

/-- f is nonconstant (follows from RealIffReal). -/
lemma nonconstant_of_realIffReal
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hreal : RealIffReal f) :
    ¬∀ z w : ℂ, f z = f w := by
  sorry

/-- f has real Taylor coefficients at real points. -/
lemma taylor_coeff_real_at_real
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hreal_fwd : ∀ x : ℝ, (f ↑x).im = 0)
    {x : ℝ} (n : ℕ) :
    (iteratedDeriv n f ↑x).im = 0 := by
  sorry

/-- Local n-to-1 structure at a critical point produces
    non-real preimages of real values. -/
lemma exists_nonreal_preimage_of_critical
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    {x₀ : ℝ} (hcrit : deriv f ↑x₀ = 0)
    (hnc : ∃ n : ℕ, 2 ≤ n ∧ iteratedDeriv n f ↑x₀ ≠ 0) :
    ∃ z : ℂ, z.im ≠ 0 ∧ (f z).im = 0 := by
  sorry

/-- The order of vanishing of f - f(x₀) at x₀ is ≥ 2
    when f'(x₀) = 0. -/
lemma order_ge_two_of_deriv_zero
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hf_nc : ¬∀ z, f z = f 0)
    {x₀ : ℝ} (hcrit : deriv f ↑x₀ = 0) :
    ∃ n : ℕ, 2 ≤ n ∧ iteratedDeriv n f ↑x₀ ≠ 0 ∧
      ∀ k, k < n → k ≥ 1 → iteratedDeriv k f ↑x₀ = 0 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Differentiable ℂ f` — entire function
- `Complex.im`, `Complex.re` — imaginary and real parts
- `Complex.ofReal` / `↑x` — embedding $\mathbb{R} \hookrightarrow \mathbb{C}$
- `iteratedDeriv n f z` — $n$-th derivative
- `deriv f z` — first derivative

**Key lemmas:**
- `AnalyticAt.order_eq_nat_iff` / `AnalyticAt.eventually_eq_zero_or_self` — order of vanishing at a point. In `Mathlib.Analysis.Analytic.IsolatedZeros`
- `AnalyticAt.eq_pow_mul` — local factorisation $f(z) - f(z_{0}) = (z-z_{0})^{n} \cdot h(z)$ with $h(z_{0}) \neq 0$
- `Complex.ofReal_im` — (↑x).im = 0 (real embedding has zero imaginary part)
- `Complex.eq_conj_iff_real` — $z$ is real iff $z = \bar{z}$
- `Differentiable.iterate_deriv` — iterated derivatives of entire functions exist
- `Complex.conj_ofReal` — conjugation fixes reals (for Schwarz reflection)
- `DifferentiableAt.hasDerivAt` — extracting derivative data

**Tactic hints:**
- `by_contra h; push_neg at h` — assume $f'(x_{0}) = 0$ for contradiction
- `obtain ⟨n, hn, hne⟩ := order_ge_two_of_deriv_zero ...` — extract the order $n \geq 2$
- `obtain ⟨z, hz_nonreal, hz_real_image⟩ := exists_nonreal_preimage_of_critical ...` — get the non-real preimage
- `exact absurd ((hreal z).mp hz_real_image) hz_nonreal` — final contradiction
- `simp [Complex.ext_iff, Complex.ofReal_im]` — relating real embedding to im = 0
- `nlinarith [Complex.sq_abs z]` — for norm computations in the local analysis
- `exact?` — finding the analytic order / isolated zeros lemma