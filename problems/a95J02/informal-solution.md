

# APM a95J02: Entire function with $|f(z)| \geq |z|^\lambda$ and $f(1) = 1$ must be $z^n$

## 1. Informal proof

**Why it's hard.** The lower bound $|f(z)| \geq |z|^\lambda$ means $f$ has no zeros except possibly at the origin, grows at least polynomially, and yet is entire. The constraint $f(1) = 1$ pins down the constant, but determining the exact function (not just its form) requires showing $\lambda$ must be a positive integer and $f$ must be a monomial.

**The key insight.** $|f(z)| \geq |z|^\lambda > 0$ for $z \neq 0$ means $f$ has no zeros away from the origin. If $f(0) = 0$, then $f(z) = z^n h(z)$ with $h$ entire and $h(0) \neq 0$. Then $|h(z)| \geq |z|^{\lambda-n}$/something. The function $1/h$ is entire ($h$ never vanishes) and bounded (since $|h| \to \infty$), forcing $h$ constant by Liouville. The normalisation $f(1) = 1$ then forces the constant to be 1 and $\lambda = n$.

**Proof.**

*Step 1: $f$ has no zeros except possibly at $z = 0$.* For $z \neq 0$: $|f(z)| \geq |z|^\lambda > 0$, so $f(z) \neq 0$.

*Step 2: $f(0) = 0$.* At $z = 0$: $|f(0)| \geq 0$ (trivially). Suppose $f(0) \neq 0$. Then $f$ never vanishes on $\mathbb{C}$, so $1/f$ is entire. And $|1/f(z)| \leq 1/|z|^\lambda \to 0$ as $|z| \to \infty$. So $1/f$ is bounded entire, hence constant by Liouville. But $1/f \to 0$ at $\infty$ forces the constant to be 0, contradicting $1/f(1) = 1$. So $f(0) = 0$.

*Step 3: Factor out the zero.* $f$ has a zero of order $n \geq 1$ at the origin: $f(z) = z^n g(z)$ where $g$ is entire and $g(0) \neq 0$.

From $|f(z)| \geq |z|^\lambda$: $|z^n g(z)| = |z|^n |g(z)| \geq |z|^\lambda$ for all $z$, so $|g(z)| \geq |z|^{\lambda-n}$ for $z \neq 0$.

*Step 4: Determine $n$ and $g$.* 

If $\lambda - n > 0$: $|g(z)| \geq |z|^{\lambda-n} \to \infty$, so $g$ has no zeros ($|g| > 0$ everywhere since $g(0) \neq 0$ and $|g(z)| \geq |z|^{\lambda-n}$ for $z \neq 0$). Then $1/g$ is entire with $|1/g(z)| \leq |z|^{n-\lambda} \to 0$ at $\infty$. Liouville gives $1/g \equiv 0$, contradiction.

If $\lambda - n < 0$: the bound $|g(z)| \geq |z|^{\lambda-n}$ is trivially satisfied for large $|z|$ (since $\lambda-n < 0$ gives $|z|^{\lambda-n} \to 0$). But we also need to check $g$ has no zeros for $z \neq 0$ (it doesn't, since $f$ has no zeros there). So $1/g$ is entire. From $|g(z)| \geq |z|^{\lambda-n}$ for $z \neq 0$ and $\lambda-n < 0$: near 0, $|g(0)| = \lim |g(z)| \geq \lim |z|^{\lambda-n} = \infty$ — wait, that's wrong since $\lambda-n < 0$ means $|z|^{\lambda-n} \to \infty$ as $z \to 0$. But $g$ is continuous at 0 with $g(0) \neq 0$ finite. Contradiction.

If $\lambda - n = 0$: $|g(z)| \geq 1$ for all $z \neq 0$. By continuity, $|g(0)| \geq 1$. So $1/g$ is entire with $|1/g| \leq 1$. By Liouville, $g$ is constant: $g(z) = c$ with $|c| \geq 1$. Then $f(z) = cz^n$. From $f(1) = 1$: $c = 1$. So **$f(z) = z^n$** where **$n = \lambda$**.

Since $\lambda$ must be a positive integer (it equals $n \in \mathbb{N}_{+}$), the answer is $f(z) = z^\lambda$ (with $\lambda$ necessarily a positive integer). ✓ ∎

**What connects.** This problem combines the classification of zeros of entire functions with Liouville's theorem. The lower bound $|f| \geq |z|^\lambda$ eliminates all zeros except at the origin and forces the zero order to exactly match the exponent $\lambda$. The Liouville argument (applied to $1/g$) converts the lower bound into rigidity, forcing $g$ to be constant. The result shows that among entire functions satisfying a power-law lower bound, the only solutions are monomials — a strong rigidity result. This connects to problem a94J08 (no entire function satisfies $|f| \geq |z|^{3/2}$, because $3/2$ is not an integer) and to the Hadamard factorisation theorem (which controls the zero structure of entire functions of finite order).

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.IsolatedZeros

open Complex

noncomputable section

/-- Main theorem: f must be z^n where n = λ (so λ is a positive integer). -/
theorem entire_lower_bound_is_monomial
    {f : ℂ → ℂ} {λ : ℝ} (hλ : 0 < λ)
    (hf : Differentiable ℂ f)
    (hf1 : f 1 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ^ λ ≤ ‖f z‖) :
    ∃ n : ℕ, 0 < n ∧ (λ = ↑n) ∧ ∀ z, f z = z ^ n := by
  sorry

/-- λ must be a positive integer. -/
lemma lambda_is_nat
    {f : ℂ → ℂ} {λ : ℝ} (hλ : 0 < λ)
    (hf : Differentiable ℂ f)
    (hbound : ∀ z : ℂ, ‖z‖ ^ λ ≤ ‖f z‖) :
    ∃ n : ℕ, 0 < n ∧ λ = ↑n := by
  sorry

/-- f has no zeros except at the origin. -/
lemma zero_only_at_origin
    {f : ℂ → ℂ} {λ : ℝ} (hλ : 0 < λ)
    (hbound : ∀ z : ℂ, ‖z‖ ^ λ ≤ ‖f z‖) :
    ∀ z : ℂ, z ≠ 0 → f z ≠ 0 := by
  sorry

/-- f(0) = 0 (from Liouville applied to 1/f). -/
lemma f_zero_eq_zero
    {f : ℂ → ℂ} {λ : ℝ} (hλ : 0 < λ)
    (hf : Differentiable ℂ f)
    (hf1 : f 1 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ^ λ ≤ ‖f z‖) :
    f 0 = 0 := by
  sorry

/-- After factoring f(z) = z^n g(z), g is constant
    with |g| ≥ 1, hence g = 1 by normalisation. -/
lemma factored_is_constant
    {f : ℂ → ℂ} {λ : ℝ} (hλ : 0 < λ)
    (hf : Differentiable ℂ f)
    (hf1 : f 1 = 1)
    (hbound : ∀ z : ℂ, ‖z‖ ^ λ ≤ ‖f z‖)
    {n : ℕ} (hn : 0 < n)
    {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hg0 : g 0 ≠ 0)
    (hfact : ∀ z, f z = z ^ n * g z)
    (hg_bound : ∀ z, z ≠ 0 → ‖z‖ ^ (λ - ↑n) ≤ ‖g z‖) :
    (λ = ↑n) ∧ ∀ z, g z = 1 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Differentiable ℂ f` — entire function
- `Real.rpow` — `‖z‖ ^ λ` for real $\lambda$ (via `NNReal.rpow` or `Real.rpow`)
- `AnalyticAt` — for analysing order of zeros

**Key lemmas:**
- `Differentiable.apply_eq_apply_of_bounded` — Liouville's theorem. Applied to $1/f$ (when $f(0)\neq 0$) and to $1/g$. In `Mathlib.Analysis.Complex.Liouville`
- `AnalyticAt.order_eq_nat_iff` — order of zero at a point is a natural number. In `Mathlib.Analysis.Analytic.IsolatedZeros`
- `AnalyticAt.eq_pow_mul_of_order_eq` — $f(z) = (z-a)^n \cdot g(z)$ with $g(a) \neq 0$
- `Differentiable.inv` — $1/f$ is differentiable where $f \neq 0$
- `norm_pow` — $\lVert z^n \rVert = \lVert z \rVert^n$
- `Real.rpow_natCast` — $\lVert z \rVert^{(\uparrow n)} = \lVert z \rVert^n$
- `norm_inv` — $\lVert f^{-1} \rVert = \lVert f \rVert^{-1}$
- `Real.rpow_pos_of_pos` — $\lVert z \rVert^\lambda > 0$ for $\lVert z \rVert > 0$

**Tactic hints:**
- `by_contra hf0; push_neg at hf0` — for $f(0) = 0$ by contradiction
- `have h_inv := Differentiable.apply_eq_apply_of_bounded ...` — Liouville on $1/f$ or $1/g$
- `obtain ⟨n, hn, g, hg, hg0, hfact⟩ := AnalyticAt.eq_pow_mul ...` — factoring out the zero
- `have : λ = ↑n := by nlinarith [...]` — pinning down $\lambda$ from the two-sided bound
- `simp [hfact, mul_comm] at hf1` — using $f(1) = 1$ to determine $g(1) = 1$
- `norm_num` — for $1^n = 1$
- `positivity` — for $\lVert z \rVert^\lambda > 0$
- `exact?` — finding Liouville