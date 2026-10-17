# APM a94J05: Liouville's theorem and its extension to bounded real part

## 1. Informal proof

**Why it's hard.** Part (a) is standard Liouville, but part (b) only assumes $\operatorname{Re} f$ is bounded below — not that $f$ itself is bounded. Since $\operatorname{Im} f$ is completely unconstrained, $f$ could a priori be unbounded, so Liouville doesn't apply directly.

**The key insight.** (a) Cauchy's integral formula for derivatives gives $|f'(z)| \leq M/R$ on circles of radius $R$; let $R \to \infty$ to get $f' \equiv 0$. (b) If $\operatorname{Re} f \geq -C$, compose with $g(z) = e^{-f(z)}$: then $|g(z)| = e^{-\operatorname{Re} f(z)} \leq e^C$, so $g$ is bounded entire, hence constant. Then $f$ is constant.

**Proof.**

**Cauchy's integral formula (statement).** If $f$ is analytic inside and on a simple closed contour $\gamma$, and $a$ is inside $\gamma$, then $f(a) = (1/2\pi i) \oint_\gamma f(z)/(z-a)\, dz$.

**(a) Liouville's theorem.** Assume $f$ is entire and $|f(z)| \leq M$ for all $z$. By the Cauchy integral formula for derivatives on the circle $|z-a| = R$:

$f'(a) = (1/2\pi i) \oint_{|z-a|=R} f(z)/(z-a)^{2}\, dz$.

The standard estimate gives $|f'(a)| \leq (1/2\pi) \cdot \max_{|z-a|=R} |f(z)|/(R^{2}) \cdot 2\pi R = M/R$.

Since this holds for all $R > 0$, letting $R \to \infty$: $|f'(a)| = 0$ for every $a \in \mathbb{C}$. So $f' \equiv 0$, hence $f$ is constant. ✓

**(b) $\operatorname{Re} f$ bounded below implies constant.** Assume $\operatorname{Re} f(z) \geq -C$ for all $z$, for some $C \geq 0$.

Define $g(z) = e^{-f(z)}$. Then $g$ is entire (composition of entire functions). Compute:

$|g(z)| = |e^{-f(z)}| = e^{-\operatorname{Re} f(z)} \leq e^{-(-C)} = e^C$.

So $g$ is a bounded entire function. By part (a), $g$ is constant: $g(z) = g(0)$ for all $z$.

Since $g(z) = e^{-f(z)} = e^{-f(0)} \neq 0$, we have $e^{-f(z)} = e^{-f(0)}$, so $-f(z)$ and $-f(0)$ differ by a multiple of $2\pi i$: $f(z) = f(0) + 2\pi ik(z)$ for some integer-valued function $k(z)$. But $f$ is continuous and $k(z) = (f(z)-f(0))/(2\pi i)$ is continuous and integer-valued, hence constant (continuous integer-valued function on connected $\mathbb{C}$ is constant). So $k(z) = k(0) = 0$, giving $f(z) = f(0)$ for all $z$. ✓ ∎

**What connects.** This is Liouville's theorem and its immediate corollary. Part (b) is often called the "Liouville theorem for $\operatorname{Re} f$ bounded below" and is proved by the exponential trick — composing with $z \mapsto e^{-z}$ to convert a half-plane bound into a disk bound. The same technique proves: if $f$ is entire and $f$ avoids a half-plane (or even a line), then $f$ is constant. This is weaker than (but implied by) Picard's little theorem (entire function omitting two values is constant). The Cauchy estimate $|f^{(n)}(a)| \leq n! M/R^{n}$ is the quantitative backbone: it converts global growth bounds into pointwise derivative bounds, and the $R \to \infty$ limit is what gives rigidity.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Metric

noncomputable section

/-- Cauchy integral formula: f(a) = (1/2πi) ∮ f(z)/(z-a) dz.
    Mathlib has this as circleIntegral-based statements. -/
lemma cauchy_integral_formula
    {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall a R)) :
    f a = (1 / (2 * π * I)) * ∮ z in C(a, R), f z / (z - a) := by
  sorry

/-- Cauchy estimate for derivatives: |f'(a)| ≤ max|f|/R. -/
lemma cauchy_deriv_bound
    {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall a R))
    {M : ℝ} (hM : ∀ z ∈ closedBall a R, ‖f z‖ ≤ M) :
    ‖deriv f a‖ ≤ M / R := by
  sorry

/-- Part (a): Liouville's theorem — bounded entire ⟹ constant. -/
theorem liouville_bounded
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) :
    ∃ c : ℂ, ∀ z, f z = c := by
  sorry

/-- Part (b): Re f bounded below ⟹ f constant. -/
theorem liouville_re_bounded_below
    {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    {C : ℝ} (hC : ∀ z, -C ≤ (f z).re) :
    ∃ c : ℂ, ∀ z, f z = c := by
  sorry

/-- The exponential composition: e^{-f} is bounded when Re f ≥ -C. -/
lemma exp_neg_bounded_of_re_bounded_below
    {f : ℂ → ℂ}
    {C : ℝ} (hC : ∀ z, -C ≤ (f z).re) :
    ∀ z, ‖exp (-f z)‖ ≤ Real.exp C := by
  sorry

/-- e^{-f} is entire when f is entire. -/
lemma differentiable_exp_neg_comp
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    Differentiable ℂ (fun z => exp (-f z)) := by
  sorry

/-- Continuous integer-valued function on connected space is constant. -/
lemma eq_of_continuous_int_valued
    {g : ℂ → ℤ} (hg : Continuous (fun z => (g z : ℂ))) :
    ∃ n : ℤ, ∀ z, g z = n := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Differentiable ℂ f` — entire function
- `Complex.exp` — complex exponential
- `Complex.re` — real part
- `Complex.I` — imaginary unit
- `circleIntegral` / `∮ z in C(a, R)` — contour integral on circles

**Key lemmas:**
- `Differentiable.apply_eq_apply_of_bounded` — Liouville's theorem in Mathlib! This is the packaged version. In `Mathlib.Analysis.Complex.Liouville`
- `Complex.norm_exp` — $\lVert e^z \rVert = e^{\operatorname{Re} z}$. Key for the exponential bound
- `Complex.norm_exp_ofReal_mul_I` — related exponential norm identities
- `Differentiable.comp` — chain rule (for $e^{-f}$)
- `differentiable_exp` — exp is entire
- `Differentiable.neg` — $-f$ is entire when $f$ is
- `Complex.ofReal_re` — extracting real part
- `isPreconnected_univ` — $\mathbb{C}$ is connected (for the integer-valued argument)
- `IsPreconnected.constant_of_mapsTo_of_isClopen` — continuous function to discrete space on connected domain is constant
- `Complex.circleIntegral.integral_sub_inv_of_mem_ball` — Cauchy integral formula in Mathlib

**Tactic hints:**
- `exact Differentiable.apply_eq_apply_of_bounded hf ⟨M, hM⟩` — direct application of Liouville for part (a) if packaged
- `have hg := liouville_bounded (differentiable_exp_neg_comp hf) ⟨exp C, exp_neg_bounded ...⟩` — applying Liouville to $e^{-f}$ for part (b)
- `simp [Complex.norm_exp, Complex.neg_re]` — simplifying $\lVert e^{-f(z)} \rVert = e^{-\operatorname{Re} f(z)}$
- `nlinarith` — for $-\operatorname{Re} f(z) \leq C$ combining bounds
- `exact?` — finding Liouville in Mathlib
- `intro z; calc` — for the exponential bound chain
- `positivity` — for $e^C > 0$
