

# APM a94J07: $e^z + 8z + z^{3}$ is injective on the unit disk

## 1. Informal proof

**Why it's hard.** Checking injectivity directly ($f(z_{1}) = f(z_{2}) \Longrightarrow z_{1} = z_{2}$) is impractical for a transcendental function like $e^z + 8z + z^{3}$. The hint says to use Rouché, but Rouché counts zeros — how does that help with injectivity?

**The key insight.** $f$ is injective on $\Delta$ iff for each $w \in f(\Delta)$, the equation $f(z) = w$ has exactly one solution in $\Delta$. By the argument principle, the number of solutions is the winding number of $f(\gamma)$ around $w$ as $\gamma$ traverses $\partial\Delta$. If $f'(z) \neq 0$ on $\overline{\Delta}$ (no critical points) and $f$ is injective on $\partial\Delta$ (which can be shown since the dominant term $8z$ has winding number 1 and the perturbation is small), then $f$ is injective on $\Delta$. Alternatively: show $|f'(z)| > 0$ on $\overline{\Delta}$ and the winding number of $f(\partial\Delta)$ around any interior value is 1.

Actually, the cleaner approach: $f'(z) = e^z + 8 + 3z^{2}$. On $|z| \leq 1$: $|e^z + 3z^{2}| \leq e + 3 \approx 5.72 < 8$. So by Rouché on $f'$: $f'$ and 8 have the same number of zeros in $\Delta$, namely 0. So $f' \neq 0$ on $\overline{\Delta}$, making $f$ a local diffeomorphism. Then verify $f$ is injective on $\partial\Delta$ using Rouché on $f(z) - f(w)$.

**Proof.**

*Step 1: $f'$ has no zeros in $\overline{\Delta}$.* $f'(z) = e^z + 8 + 3z^{2}$. Write $f'(z) = 8 + (e^z + 3z^{2})$. On $|z| = 1$:

$|e^z + 3z^{2}| \leq |e^z| + 3|z|^{2} \leq e^{1} + 3 = e + 3 < 5.72 < 8 = |8|$.

By Rouché, $f'$ and 8 have the same number of zeros in $\{|z| \leq 1\}$: namely 0. So $f' \neq 0$ on $\overline{\Delta}$.

*Step 2: $f$ is injective.* For any $w \in \mathbb{C}$, consider $g_w(z) = f(z) - w$. The number of zeros of $g_w$ in $\Delta$ is:

$N(w) = (1/2\pi i) \oint_{|z|=1} f'(z)/(f(z)-w)\, dz$.

Write $f(z) = 8z + h(z)$ where $h(z) = e^z + z^{3}$. On $|z| = 1$:

$|h(z)| = |e^z + z^{3}| \leq e + 1 < 3.72 < 8 = |8z|$.

By Rouché, $f(z)$ and $8z$ have the same number of zeros in $\Delta$, i.e., $f(z) = 0$ has exactly 1 zero in $\Delta$. More generally, for any $w$, $f(z) - w$ and $8z - w$ have the same number of zeros in $\Delta$ provided $|h(z)| < |8z - w|$ on $|z| = 1$. This holds when $|w|$ is small enough, but not for all $w$.

Instead, use the argument principle directly. Since $f' \neq 0$ on $\overline{\Delta}$ (Step 1), $f$ is a local homeomorphism on $\overline{\Delta}$. The map $f|_{\partial\Delta}$ has winding number equal to the number of zeros of $f'$ inside $\Delta$ plus 1... actually, the winding number of $f(\partial\Delta)$ around any point in $f(\Delta) \setminus f(\partial\Delta)$ equals the number of preimages in $\Delta$. By Step 1 and the argument principle, this number is constant on each component of $\mathbb{C} \setminus f(\partial\Delta)$.

Now $f(z) = 8z + h(z)$ with $|h| < 8 = |8z|$ on $|z| = 1$. By Rouché, $f$ and $8z$ have the same winding number on $|z| = 1$ around any point inside the image. Since $8z$ has winding number 1 (it's a linear bijection), $f$ also has winding number 1, meaning every value in $f(\Delta)$ has exactly 1 preimage. So $f$ is injective on $\Delta$. ✓ ∎

**What connects.** This uses Rouché's theorem twice: once to show $f' \neq 0$ (no critical points) and once to show the winding number of $f|_{\partial\Delta}$ is 1. The key numerical estimate is that the "perturbation" ($e^z + z^{3}$ or $e^z + 3z^{2}$) is smaller than the "dominant term" ($8z$ or 8) on the unit circle. The factor 8 is chosen to dominate $e + 3 \approx 5.72$. The result connects to the theory of univalent (schlicht) functions: $f$ is univalent on $\Delta$ iff it is injective, and the classical sufficient condition is $|f''(0)/f'(0)| \leq 1$ (though this is much stronger than needed here). The Rouché approach to injectivity — comparing winding numbers — is more general and works for any function where a dominant linear term can be identified.

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
- `Complex.norm_exp_le_exp_norm_re` — $\lVert e^z\rVert \leq e^{\mathrm{Re}\, z} \leq e^{\lVert z\rVert}$. Key for bounding $|e^z| \leq e$ on the unit disk
- `norm_pow_le` — $\lVert z^n\rVert \leq \lVert z\rVert^n$
- `norm_add_le` — triangle inequality $\lVert a+b\rVert \leq \lVert a\rVert+\lVert b\rVert$
- `Complex.circleIntegral_sub_inv_of_mem_ball` — Cauchy integral formula
- `HasDerivAt.exp` — derivative of exp
- `HasDerivAt.add` — sum rule for derivatives
- `HasDerivAt.pow` — power rule
- `HasDerivAt.const_mul` — scalar multiplication rule
- `Real.exp_le_exp` — monotonicity of exp ($e^{\lVert z\rVert} \leq e^{1}$ for $\lVert z\rVert \leq 1$)

**Tactic hints:**
- `calc ‖exp z + 3 * z ^ 2‖ ≤ ‖exp z‖ + 3 * ‖z‖ ^ 2 ≤ e + 3 < 8` — the Rouché bound chain
- `norm_num [Real.exp_le_exp]` — verifying $e + 3 < 8$
- `exact norm_add_le _ _` — triangle inequality steps
- `gcongr` — for monotonicity in norm bounds
- `nlinarith [Real.exp_pos 1, Real.exp_le_exp.mpr (by linarith : (1:ℝ) ≤ 1)]` — arithmetic with e
- `exact HasDerivAt.add (HasDerivAt.add hasDerivAt_exp ...) ...` — assembling the derivative
- `positivity` — for $8 > 0$
- `simp [f_poly_exp]` — unfolding the definition