

# APM a94J05: Liouville's theorem and its extension to bounded real part

## 1. Informal proof

**Why it's hard.** Part (a) is standard Liouville, but part (b) only assumes Re f is bounded below — not that f itself is bounded. Since Im f is completely unconstrained, f could a priori be unbounded, so Liouville doesn't apply directly.

**The key insight.** (a) Cauchy's integral formula for derivatives gives |f'(z)| ≤ M/R on circles of radius R; let R → ∞ to get f' ≡ 0. (b) If Re f ≥ -C, compose with g(z) = e^{-f(z)}: then |g(z)| = e^{-Re f(z)} ≤ e^C, so g is bounded entire, hence constant. Then f is constant.

**Proof.**

**Cauchy's integral formula (statement).** If f is analytic inside and on a simple closed contour γ, and a is inside γ, then f(a) = (1/2πi) ∮_γ f(z)/(z-a) dz.

**(a) Liouville's theorem.** Assume f is entire and |f(z)| ≤ M for all z. By the Cauchy integral formula for derivatives on the circle |z-a| = R:

f'(a) = (1/2πi) ∮_{|z-a|=R} f(z)/(z-a)² dz.

The standard estimate gives |f'(a)| ≤ (1/2π) · max_{|z-a|=R} |f(z)|/(R²) · 2πR = M/R.

Since this holds for all R > 0, letting R → ∞: |f'(a)| = 0 for every a ∈ ℂ. So f' ≡ 0, hence f is constant. ✓

**(b) Re f bounded below implies constant.** Assume Re f(z) ≥ -C for all z, for some C ≥ 0.

Define g(z) = e^{-f(z)}. Then g is entire (composition of entire functions). Compute:

|g(z)| = |e^{-f(z)}| = e^{-Re f(z)} ≤ e^{-(-C)} = e^C.

So g is a bounded entire function. By part (a), g is constant: g(z) = g(0) for all z.

Since g(z) = e^{-f(z)} = e^{-f(0)} ≠ 0, we have e^{-f(z)} = e^{-f(0)}, so -f(z) and -f(0) differ by a multiple of 2πi: f(z) = f(0) + 2πik(z) for some integer-valued function k(z). But f is continuous and k(z) = (f(z)-f(0))/(2πi) is continuous and integer-valued, hence constant (continuous integer-valued function on connected ℂ is constant). So k(z) = k(0) = 0, giving f(z) = f(0) for all z. ✓ ∎

**What connects.** This is Liouville's theorem and its immediate corollary. Part (b) is often called the "Liouville theorem for Re f bounded below" and is proved by the exponential trick — composing with z ↦ e^{-z} to convert a half-plane bound into a disk bound. The same technique proves: if f is entire and f avoids a half-plane (or even a line), then f is constant. This is weaker than (but implied by) Picard's little theorem (entire function omitting two values is constant). The Cauchy estimate |f^{(n)}(a)| ≤ n! M/Rⁿ is the quantitative backbone: it converts global growth bounds into pointwise derivative bounds, and the R → ∞ limit is what gives rigidity.

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
- `Complex.norm_exp` — ‖e^z‖ = e^{Re z}. Key for the exponential bound
- `Complex.norm_exp_ofReal_mul_I` — related exponential norm identities
- `Differentiable.comp` — chain rule (for e^{-f})
- `differentiable_exp` — exp is entire
- `Differentiable.neg` — -f is entire when f is
- `Complex.ofReal_re` — extracting real part
- `isPreconnected_univ` — ℂ is connected (for the integer-valued argument)
- `IsPreconnected.constant_of_mapsTo_of_isClopen` — continuous function to discrete space on connected domain is constant
- `Complex.circleIntegral.integral_sub_inv_of_mem_ball` — Cauchy integral formula in Mathlib

**Tactic hints:**
- `exact Differentiable.apply_eq_apply_of_bounded hf ⟨M, hM⟩` — direct application of Liouville for part (a) if packaged
- `have hg := liouville_bounded (differentiable_exp_neg_comp hf) ⟨exp C, exp_neg_bounded ...⟩` — applying Liouville to e^{-f} for part (b)
- `simp [Complex.norm_exp, Complex.neg_re]` — simplifying ‖e^{-f(z)}‖ = e^{-Re f(z)}
- `nlinarith` — for -Re f(z) ≤ C combining bounds
- `exact?` — finding Liouville in Mathlib
- `intro z; calc` — for the exponential bound chain
- `positivity` — for e^C > 0