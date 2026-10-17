

# APM a02J07: Winding number constraints from a path avoiding the positive real axis

## Why It's Hard

The integral $\int_\gamma dz/z$ computes a *branch of the logarithm* along $\gamma$: it equals $\log(\gamma(1)/\gamma(0))$ for a suitable branch, with the imaginary part being the total change in argument. The constraint $\gamma^{-1}([0,\infty)) = \{0\}$ means the path starts at $\pi$ (a positive real number) and *never returns to the nonneg real axis*. This constrains how much the argument can wind: it can't complete a full loop (which would require crossing $[0,\infty)$ again) but it must leave the real axis (since $\gamma(t) \notin [0,\infty)$ for $t > 0$). The difficulty is making this topological intuition into a rigorous analytic argument.

## The Key Insight

Since $\gamma$ avoids $[0,\infty)$ for $t > 0$, the path lies entirely in $\mathbb{C} \setminus [0,\infty)$ after leaving the starting point. On this slit domain, a single-valued branch of $\log z$ (hence of $\arg z$) exists, taking values in $(0, 2\pi)$. The imaginary part of $\int_\gamma dz/z$ equals $\arg(\gamma(1)) - \arg(\gamma(0))$. Since $\gamma(0) = \pi > 0$, $\arg(\gamma(0))$ approaches either $0^{+}$ or $2\pi^{-}$ (limits from above or below the slit). Since $\gamma(1) \in \mathbb{C} \setminus [0,\infty)$, $\arg(\gamma(1)) \in (0, 2\pi)$ strictly. The bounds follow.

## Complete Proof

**Theorem.** Let $\gamma : [0,1] \to \mathbb{C}$ be piecewise smooth with $\gamma(0) = \pi$ and $\gamma^{-1}([0,\infty)) = \{0\}$. Then $0 < |\text{Im} \int_\gamma dz/z| < 2\pi$.

**Proof.**

**Step 1: A branch of $\log$ exists along $\gamma|(0,1]$.**

The domain $\Omega = \mathbb{C} \setminus [0,\infty)$ is simply connected, and $1/z$ is holomorphic on $\Omega$. Define the principal logarithm on $\Omega$:

$$\text{Log}_*(z) = \ln|z| + i\arg_*(z), \quad \arg_*(z) \in (0, 2\pi),$$

where $\arg_*$ is the argument with branch cut on $[0,\infty)$ (so $\arg_*$ is continuous on $\Omega$ with values in $(0,2\pi)$).

For $t \in (0,1]$, $\gamma(t) \in \mathbb{C} \setminus [0,\infty) = \Omega$ (since $\gamma^{-1}([0,\infty)) = \{0\}$). So $\text{Log}_* \circ \gamma$ is well-defined and continuous on $(0,1]$.

**Step 2: Compute the integral.**

Since $d(\text{Log}_* z) = dz/z$ on $\Omega$:

$$\int_\gamma \frac{dz}{z} = \lim_{\varepsilon \to 0^+}\int_{\varepsilon}^{1}\frac{\gamma'(t)}{\gamma(t)}\,dt = \lim_{\varepsilon \to 0^+}\left[\text{Log}_*(\gamma(t))\right]_{t=\varepsilon}^{t=1} = \text{Log}_*(\gamma(1)) - \lim_{\varepsilon \to 0^+}\text{Log}_*(\gamma(\varepsilon)).$$

Now $\gamma(0) = \pi > 0$, and $\gamma$ is continuous, so $\gamma(\epsilon) \to \pi$ as $\epsilon \to 0^{+}$. Since $\gamma(\epsilon) \notin [0,\infty)$ for $\epsilon > 0$, $\gamma(\epsilon)$ approaches $\pi$ from either the upper or lower half-plane.

**Case 1: $\gamma$ enters the upper half-plane** ($\text{Im} \gamma(\epsilon) > 0$ for small $\epsilon > 0$). Then $\arg_*(\gamma(\epsilon)) \to 0^{+}$ as $\epsilon \to 0^{+}$ (since $\arg_*$ of a point just above the positive real axis is close to 0, using our convention $\arg_* \in (0,2\pi)$ — actually for points just above the positive real axis, the argument is close to 0 from above, but in our branch $\arg_* \in (0,2\pi)$, so $\arg_* \to 0^{+}$).

Wait, I need to be careful. With $\arg_* \in (0,2\pi)$ and branch cut on $[0,\infty)$:
- Points just above the positive real axis: $\arg_* \to 0^{+}$.
- Points just below the positive real axis: $\arg_* \to 2\pi^{-}$.

So: if $\gamma$ enters the upper half-plane, $\lim \arg_*(\gamma(\epsilon)) = 0^{+}$, and $\lim \text{Log}_*(\gamma(\epsilon)) = \ln(\pi) + i\cdot 0 = \ln \pi$.

If $\gamma$ enters the lower half-plane, $\lim \arg_*(\gamma(\epsilon)) = 2\pi^{-}$, and $\lim \text{Log}_*(\gamma(\epsilon)) = \ln(\pi) + 2\pi i$.

**Step 3: Compute $\text{Im} \int_\gamma dz/z$.**

$$\text{Im}\int_\gamma \frac{dz}{z} = \arg_*(\gamma(1)) - \lim_{\varepsilon\to 0^+}\arg_*(\gamma(\varepsilon)).$$

**Case 1 ($\gamma$ exits upward):** $\text{Im} \int = \arg_*(\gamma(1)) - 0 = \arg_*(\gamma(1)) \in (0, 2\pi)$. Since $\gamma(1) \in \Omega$, $\arg_*(\gamma(1))$ is strictly between 0 and $2\pi$. So:

$$0 < \text{Im}\int_\gamma \frac{dz}{z} < 2\pi.$$

**Case 2 ($\gamma$ exits downward):** $\text{Im} \int = \arg_*(\gamma(1)) - 2\pi \in (-2\pi, 0)$. So:

$$-2\pi < \text{Im}\int_\gamma \frac{dz}{z} < 0.$$

**In both cases:** $0 < |\text{Im} \int_\gamma dz/z| < 2\pi$. ✓

**Step 4: Verify the strict inequalities.**

*Lower bound ($\text{Im} \neq 0$):* If $\text{Im} \int = 0$, then in Case 1, $\arg_*(\gamma(1)) = 0$, which would put $\gamma(1)$ on $[0,\infty)$, contradicting $\gamma(1) \in \Omega$. In Case 2, $\arg_*(\gamma(1)) = 2\pi$, same contradiction. So $\text{Im} \int \neq 0$. ✓

*Upper bound ($|\text{Im}| < 2\pi$):* In Case 1, $\arg_*(\gamma(1)) < 2\pi$ strictly (since $\gamma(1) \in \Omega$). In Case 2, $\arg_*(\gamma(1)) > 0$ strictly. So $|\text{Im} \int| < 2\pi$. ✓

Therefore $0 < |\text{Im} \int_\gamma dz/z| < 2\pi$. ∎

## What Connects

**To the winding number.** $\text{Im}(\int_\gamma dz/z)$ = change in $\arg(z)$ along $\gamma$, which equals $2\pi$ times the winding number of $\gamma$ around 0 *plus* the argument of the endpoint relative to the starting point. The constraint that $\gamma$ avoids $[0,\infty)$ prevents a full winding (which would require crossing the branch cut), limiting the total argument change to strictly between 0 and $2\pi$ in absolute value.

**To the monodromy theorem.** The existence of a single-valued branch of $\log z$ along $\gamma$ is guaranteed by the monodromy theorem: the path $\gamma|(0,1]$ lies in the simply connected domain $\mathbb{C} \setminus [0,\infty)$, so any holomorphic function (including any branch of $\log$) can be analytically continued along it without monodromy.

**To the argument principle.** $\int_\gamma dz/z = \sum$ (winding numbers around poles of $1/z$) $\times 2\pi i = 2\pi i \cdot n(\gamma, 0)$. But $\gamma$ is not closed, so the winding number is not an integer — it's a real number in $(-1, 0) \cup (0, 1)$, consistent with $|\text{Im}| \in (0, 2\pi)$.

**To branch cut geometry.** The condition $\gamma^{-1}([0,\infty)) = \{0\}$ is precisely the condition that $\gamma$ can be lifted to the Riemann surface of $\log z$ without crossing the sheet boundary. The lift starts at $\ln(\pi) + 0i$ or $\ln(\pi) + 2\pi i$ and ends at a point with imaginary part strictly between these, hence the bounds.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open Complex Set Filter

noncomputable section

/-- The path hypotheses: piecewise smooth, starts at π, and only
    hits [0,∞) at time t = 0. -/
structure SlitPath (γ : ℝ → ℂ) : Prop where
  start : γ 0 = π
  avoids : ∀ t ∈ Ioc (0 : ℝ) 1, ¬(γ t).im = 0 ∨ (γ t).re < 0
  -- more precisely: γ(t) ∉ [0,∞) for t ∈ (0,1]
  avoids_nonneg_real : ∀ t ∈ Ioc (0 : ℝ) 1,
    ¬((γ t).im = 0 ∧ 0 ≤ (γ t).re)
  continuous : Continuous γ
  piecewise_smooth : ∀ t ∈ Icc (0 : ℝ) 1,
    DifferentiableAt ℝ γ t ∨ t ∈ ({0, 1} : Set ℝ) -- simplified
  nonzero : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0

/-- The contour integral ∫_γ dz/z. -/
def logIntegral (γ : ℝ → ℂ) : ℂ :=
  ∫ t in Icc (0 : ℝ) 1, deriv γ t / γ t

/-- The argument function with values in (0, 2π), defined on ℂ \ [0,∞). -/
def arg_star (z : ℂ) : ℝ :=
  if 0 < z.im then z.arg  -- arg ∈ (0, π)
  else if z.im < 0 then z.arg + 2 * Real.pi  -- arg ∈ (π, 2π)
  else if z.re < 0 then Real.pi  -- negative real axis
  else 0  -- shouldn't occur on ℂ \ [0,∞)

/-- arg_star is continuous on ℂ \ [0,∞). -/
lemma arg_star_continuous :
    ContinuousOn arg_star {z : ℂ | ¬(z.im = 0 ∧ 0 ≤ z.re)} := by
  sorry

/-- The integral equals Log*(γ(1)) - lim Log*(γ(ε)). -/
lemma logIntegral_eq_diff (γ : ℝ → ℂ) (hγ : SlitPath γ) :
    (logIntegral γ).im =
      arg_star (γ 1) - limUnder (𝓝[>] 0) (fun t => arg_star (γ t)) := by
  sorry

/-- If γ exits upward: lim_{ε→0+} arg*(γ(ε)) = 0. -/
lemma arg_star_limit_upper (γ : ℝ → ℂ) (hγ : SlitPath γ)
    (h_up : ∀ᶠ t in 𝓝[>] 0, 0 < (γ t).im) :
    Tendsto (fun t => arg_star (γ t)) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- If γ exits downward: lim_{ε→0+} arg*(γ(ε)) = 2π. -/
lemma arg_star_limit_lower (γ : ℝ → ℂ) (hγ : SlitPath γ)
    (h_down : ∀ᶠ t in 𝓝[>] 0, (γ t).im < 0) :
    Tendsto (fun t => arg_star (γ t)) (𝓝[>] 0) (𝓝 (2 * Real.pi)) := by
  sorry

/-- arg*(γ(1)) ∈ (0, 2π) strictly, since γ(1) ∉ [0,∞). -/
lemma arg_star_endpoint_bounds (γ : ℝ → ℂ) (hγ : SlitPath γ) :
    0 < arg_star (γ 1) ∧ arg_star (γ 1) < 2 * Real.pi := by
  sorry

/-- Lower bound: |Im ∫_γ dz/z| > 0. -/
theorem logIntegral_im_ne_zero (γ : ℝ → ℂ) (hγ : SlitPath γ) :
    (logIntegral γ).im ≠ 0 := by
  sorry

/-- Upper bound: |Im ∫_γ dz/z| < 2π. -/
theorem logIntegral_im_lt_two_pi (γ : ℝ → ℂ) (hγ : SlitPath γ) :
    |(logIntegral γ).im| < 2 * Real.pi := by
  sorry

/-- Main theorem: 0 < |Im ∫_γ dz/z| < 2π. -/
theorem logIntegral_im_bounds (γ : ℝ → ℂ) (hγ : SlitPath γ) :
    0 < |(logIntegral γ).im| ∧ |(logIntegral γ).im| < 2 * Real.pi := by
  sorry

end
```

**Mathlib notes:**

- `SlitPath` bundles the hypotheses: $\gamma$ starts at $\pi$, $\gamma(t) \notin [0,\infty)$ for $t > 0$, $\gamma$ is continuous and piecewise smooth, and $\gamma$ never hits 0. The "avoids nonneg real" condition is `¬(im = 0 ∧ re ≥ 0)`, which is `γ(t) ∉ [0,∞)` embedded in $\mathbb{C}$.
- `logIntegral γ` is defined as `∫ t in [0,1], γ'(t)/γ(t) dt` — the standard contour integral of $dz/z$.
- `arg_star` is the argument function with range $(0, 2\pi)$, continuous on $\mathbb{C} \setminus [0,\infty)$. This differs from Mathlib's `Complex.arg` which has range $(-\pi, \pi]$.
- The proof hinges on whether $\gamma$ initially enters the upper or lower half-plane (determining the limiting value of $\arg_*$ at $t = 0^{+}$), combined with `arg_star_endpoint_bounds` ($\gamma(1) \in \Omega$ implies strict bounds on $\arg_*(\gamma(1))$).
- `limUnder (𝓝[>] 0) f` is the limit of $f$ along the right-neighborhood filter of 0 — the one-sided limit as $t \to 0^{+}$.
