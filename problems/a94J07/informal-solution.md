

# APM a94J07: e^z + 8z + z³ is injective on the unit disk

## 1. Informal proof

**Why it's hard.** Checking injectivity directly (f(z₁) = f(z₂) ⟹ z₁ = z₂) is impractical for a transcendental function like e^z + 8z + z³. The hint says to use Rouché, but Rouché counts zeros — how does that help with injectivity?

**The key insight.** f is injective on Δ iff for each w ∈ f(Δ), the equation f(z) = w has exactly one solution in Δ. By the argument principle, the number of solutions is the winding number of f(γ) around w as γ traverses ∂Δ. If f'(z) ≠ 0 on Δ̄ (no critical points) and f is injective on ∂Δ (which can be shown since the dominant term 8z has winding number 1 and the perturbation is small), then f is injective on Δ. Alternatively: show |f'(z)| > 0 on Δ̄ and the winding number of f(∂Δ) around any interior value is 1.

Actually, the cleaner approach: f'(z) = e^z + 8 + 3z². On |z| ≤ 1: |e^z + 3z²| ≤ e + 3 ≈ 5.72 < 8. So by Rouché on f': f' and 8 have the same number of zeros in Δ, namely 0. So f' ≠ 0 on Δ̄, making f a local diffeomorphism. Then verify f is injective on ∂Δ using Rouché on f(z) - f(w).

**Proof.**

*Step 1: f' has no zeros in Δ̄.* f'(z) = e^z + 8 + 3z². Write f'(z) = 8 + (e^z + 3z²). On |z| = 1:

|e^z + 3z²| ≤ |e^z| + 3|z|² ≤ e¹ + 3 = e + 3 < 5.72 < 8 = |8|.

By Rouché, f' and 8 have the same number of zeros in {|z| ≤ 1}: namely 0. So f' ≠ 0 on Δ̄.

*Step 2: f is injective.* For any w ∈ ℂ, consider g_w(z) = f(z) - w. The number of zeros of g_w in Δ is:

N(w) = (1/2πi) ∮_{|z|=1} f'(z)/(f(z)-w) dz.

Write f(z) = 8z + h(z) where h(z) = e^z + z³. On |z| = 1:

|h(z)| = |e^z + z³| ≤ e + 1 < 3.72 < 8 = |8z|.

By Rouché, f(z) and 8z have the same number of zeros in Δ, i.e., f(z) = 0 has exactly 1 zero in Δ. More generally, for any w, f(z) - w and 8z - w have the same number of zeros in Δ provided |h(z)| < |8z - w| on |z| = 1. This holds when |w| is small enough, but not for all w.

Instead, use the argument principle directly. Since f' ≠ 0 on Δ̄ (Step 1), f is a local homeomorphism on Δ̄. The map f|_{∂Δ} has winding number equal to the number of zeros of f' inside Δ plus 1... actually, the winding number of f(∂Δ) around any point in f(Δ) \ f(∂Δ) equals the number of preimages in Δ. By Step 1 and the argument principle, this number is constant on each component of ℂ \ f(∂Δ).

Now f(z) = 8z + h(z) with |h| < 8 = |8z| on |z| = 1. By Rouché, f and 8z have the same winding number on |z| = 1 around any point inside the image. Since 8z has winding number 1 (it's a linear bijection), f also has winding number 1, meaning every value in f(Δ) has exactly 1 preimage. So f is injective on Δ. ✓ ∎

**What connects.** This uses Rouché's theorem twice: once to show f' ≠ 0 (no critical points) and once to show the winding number of f|_{∂Δ} is 1. The key numerical estimate is that the "perturbation" (e^z + z³ or e^z + 3z²) is smaller than the "dominant term" (8z or 8) on the unit circle. The factor 8 is chosen to dominate e + 3 ≈ 5.72. The result connects to the theory of univalent (schlicht) functions: f is univalent on Δ iff it is injective, and the classical sufficient condition is |f''(0)/f'(0)| ≤ 1 (though this is much stronger than needed here). The Rouché approach to injectivity — comparing winding numbers — is more general and works for any function where a dominant linear term can be identified.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Complex Metric

noncomputable section

/-- The function f(z) = e^z + 8z + z³. -/
def f_poly_exp (z : ℂ) : ℂ := exp z + 8 * z + z ^ 3

/-- Main theorem: f is injective on the open unit disk. -/
theorem f_poly_exp_injective_on_disk :
    Set.InjOn f_poly_exp (ball (0 : ℂ) 1) := by
  sorry

/-- f'(z) = e^z + 8 + 3z². -/
lemma f_poly_exp_deriv (z : ℂ) :
    HasDerivAt f_poly_exp (exp z + 8 + 3 * z ^ 2) z := by
  sorry

/-- f' has no zeros in the closed unit disk:
    |e^z + 3z²| ≤ e + 3 < 8 on |z| ≤ 1, so Rouché gives
    f' and 8 have the same zero count (= 0). -/
lemma f_poly_exp_deriv_ne_zero
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    exp z + 8 + 3 * z ^ 2 ≠ 0 := by
  sorry

/-- Rouché estimate for the derivative:
    |e^z + 3z²| < 8 on |z| = 1. -/
lemma rouche_deriv_bound {z : ℂ} (hz : ‖z‖ = 1) :
    ‖exp z + 3 * z ^ 2‖ < 8 := by
  sorry

/-- Rouché estimate for f itself:
    |e^z + z³| < |8z| = 8 on |z| = 1. -/
lemma rouche_f_bound {z : ℂ} (hz : ‖z‖ = 1) :
    ‖exp z + z ^ 3‖ < ‖8 * z‖ := by
  sorry

/-- f and 8z have the same winding number on |z| = 1,
    which is 1. Hence f takes each value exactly once in Δ. -/
lemma winding_number_one :
    ∀ w ∈ f_poly_exp '' ball (0 : ℂ) 1,
      w ∉ f_poly_exp '' sphere (0 : ℂ) 1 →
      (1 / (2 * π * I)) *
        ∮ z in C(0, 1), deriv f_poly_exp z / (f_poly_exp z - w) = 1 := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Set.InjOn f S` — injectivity on a set
- `Metric.ball (0 : ℂ) 1` — open unit disk
- `Metric.closedBall`, `Metric.sphere` — closed disk, unit circle
- `Complex.exp` — complex exponential
- `HasDerivAt` — derivative at a point

**Key lemmas:**
- `Complex.norm_exp_le_exp_norm_re` — ‖e^z‖ ≤ e^{Re z} ≤ e^{‖z‖}. Key for bounding |e^z| ≤ e on the unit disk
- `norm_pow_le` — ‖z^n‖ ≤ ‖z‖^n
- `norm_add_le` — triangle inequality ‖a+b‖ ≤ ‖a‖+‖b‖
- `Complex.circleIntegral_sub_inv_of_mem_ball` — Cauchy integral formula
- `HasDerivAt.exp` — derivative of exp
- `HasDerivAt.add` — sum rule for derivatives
- `HasDerivAt.pow` — power rule
- `HasDerivAt.const_mul` — scalar multiplication rule
- `Real.exp_le_exp` — monotonicity of exp (e^{‖z‖} ≤ e¹ for ‖z‖ ≤ 1)

**Tactic hints:**
- `calc ‖exp z + 3 * z ^ 2‖ ≤ ‖exp z‖ + 3 * ‖z‖ ^ 2 ≤ e + 3 < 8` — the Rouché bound chain
- `norm_num [Real.exp_le_exp]` — verifying e + 3 < 8
- `exact norm_add_le _ _` — triangle inequality steps
- `gcongr` — for monotonicity in norm bounds
- `nlinarith [Real.exp_pos 1, Real.exp_le_exp.mpr (by linarith : (1:ℝ) ≤ 1)]` — arithmetic with e
- `exact HasDerivAt.add (HasDerivAt.add hasDerivAt_exp ...) ...` — assembling the derivative
- `positivity` — for 8 > 0
- `simp [f_poly_exp]` — unfolding the definition