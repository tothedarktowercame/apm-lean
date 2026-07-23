

# APM a02J07: Winding number constraints from a path avoiding the positive real axis

## Why It's Hard

The integral ∫\_γ dz/z computes a *branch of the logarithm* along γ: it equals log(γ(1)/γ(0)) for a suitable branch, with the imaginary part being the total change in argument. The constraint γ⁻¹([0,∞)) = {0} means the path starts at π (a positive real number) and *never returns to the nonneg real axis*. This constrains how much the argument can wind: it can't complete a full loop (which would require crossing [0,∞) again) but it must leave the real axis (since γ(t) ∉ [0,∞) for t > 0). The difficulty is making this topological intuition into a rigorous analytic argument.

## The Key Insight

Since γ avoids [0,∞) for t > 0, the path lies entirely in ℂ \ [0,∞) after leaving the starting point. On this slit domain, a single-valued branch of log z (hence of arg z) exists, taking values in (0, 2π). The imaginary part of ∫\_γ dz/z equals arg(γ(1)) - arg(γ(0)). Since γ(0) = π > 0, arg(γ(0)) approaches either 0⁺ or 2π⁻ (limits from above or below the slit). Since γ(1) ∈ ℂ \ [0,∞), arg(γ(1)) ∈ (0, 2π) strictly. The bounds follow.

## Complete Proof

**Theorem.** Let γ : [0,1] → ℂ be piecewise smooth with γ(0) = π and γ⁻¹([0,∞)) = {0}. Then 0 < |Im ∫\_γ dz/z| < 2π.

**Proof.**

**Step 1: A branch of log exists along γ|(0,1].**

The domain Ω = ℂ \ [0,∞) is simply connected, and 1/z is holomorphic on Ω. Define the principal logarithm on Ω:

$$\text{Log}_*(z) = \ln|z| + i\arg_*(z), \quad \arg_*(z) \in (0, 2\pi),$$

where arg\_\* is the argument with branch cut on [0,∞) (so arg\_\* is continuous on Ω with values in (0,2π)).

For t ∈ (0,1], γ(t) ∈ ℂ \ [0,∞) = Ω (since γ⁻¹([0,∞)) = {0}). So Log\_\* ∘ γ is well-defined and continuous on (0,1].

**Step 2: Compute the integral.**

Since d(Log\_\* z) = dz/z on Ω:

$$\int_\gamma \frac{dz}{z} = \lim_{\varepsilon \to 0^+}\int_{\varepsilon}^{1}\frac{\gamma'(t)}{\gamma(t)}\,dt = \lim_{\varepsilon \to 0^+}\left[\text{Log}_*(\gamma(t))\right]_{t=\varepsilon}^{t=1} = \text{Log}_*(\gamma(1)) - \lim_{\varepsilon \to 0^+}\text{Log}_*(\gamma(\varepsilon)).$$

Now γ(0) = π > 0, and γ is continuous, so γ(ε) → π as ε → 0⁺. Since γ(ε) ∉ [0,∞) for ε > 0, γ(ε) approaches π from either the upper or lower half-plane.

**Case 1: γ enters the upper half-plane** (Im γ(ε) > 0 for small ε > 0). Then arg\_\*(γ(ε)) → 0⁺ as ε → 0⁺ (since arg\_\* of a point just above the positive real axis is close to 0, using our convention arg\_\* ∈ (0,2π) — actually for points just above the positive real axis, the argument is close to 0 from above, but in our branch arg\_\* ∈ (0,2π), so arg\_\* → 0⁺).

Wait, I need to be careful. With arg\_\* ∈ (0,2π) and branch cut on [0,∞):
- Points just above the positive real axis: arg\_\* → 0⁺.
- Points just below the positive real axis: arg\_\* → 2π⁻.

So: if γ enters the upper half-plane, lim arg\_\*(γ(ε)) = 0⁺, and lim Log\_\*(γ(ε)) = ln(π) + i·0 = ln π.

If γ enters the lower half-plane, lim arg\_\*(γ(ε)) = 2π⁻, and lim Log\_\*(γ(ε)) = ln(π) + 2πi.

**Step 3: Compute Im ∫\_γ dz/z.**

$$\text{Im}\int_\gamma \frac{dz}{z} = \arg_*(\gamma(1)) - \lim_{\varepsilon\to 0^+}\arg_*(\gamma(\varepsilon)).$$

**Case 1 (γ exits upward):** Im ∫ = arg\_\*(γ(1)) - 0 = arg\_\*(γ(1)) ∈ (0, 2π). Since γ(1) ∈ Ω, arg\_\*(γ(1)) is strictly between 0 and 2π. So:

$$0 < \text{Im}\int_\gamma \frac{dz}{z} < 2\pi.$$

**Case 2 (γ exits downward):** Im ∫ = arg\_\*(γ(1)) - 2π ∈ (-2π, 0). So:

$$-2\pi < \text{Im}\int_\gamma \frac{dz}{z} < 0.$$

**In both cases:** 0 < |Im ∫\_γ dz/z| < 2π. ✓

**Step 4: Verify the strict inequalities.**

*Lower bound (Im ≠ 0):* If Im ∫ = 0, then in Case 1, arg\_\*(γ(1)) = 0, which would put γ(1) on [0,∞), contradicting γ(1) ∈ Ω. In Case 2, arg\_\*(γ(1)) = 2π, same contradiction. So Im ∫ ≠ 0. ✓

*Upper bound (|Im| < 2π):* In Case 1, arg\_\*(γ(1)) < 2π strictly (since γ(1) ∈ Ω). In Case 2, arg\_\*(γ(1)) > 0 strictly. So |Im ∫| < 2π. ✓

Therefore 0 < |Im ∫\_γ dz/z| < 2π. ∎

## What Connects

**To the winding number.** Im(∫\_γ dz/z) = change in arg(z) along γ, which equals 2π times the winding number of γ around 0 *plus* the argument of the endpoint relative to the starting point. The constraint that γ avoids [0,∞) prevents a full winding (which would require crossing the branch cut), limiting the total argument change to strictly between 0 and 2π in absolute value.

**To the monodromy theorem.** The existence of a single-valued branch of log z along γ is guaranteed by the monodromy theorem: the path γ|(0,1] lies in the simply connected domain ℂ \ [0,∞), so any holomorphic function (including any branch of log) can be analytically continued along it without monodromy.

**To the argument principle.** ∫\_γ dz/z = Σ (winding numbers around poles of 1/z) × 2πi = 2πi · n(γ, 0). But γ is not closed, so the winding number is not an integer — it's a real number in (-1, 0) ∪ (0, 1), consistent with |Im| ∈ (0, 2π).

**To branch cut geometry.** The condition γ⁻¹([0,∞)) = {0} is precisely the condition that γ can be lifted to the Riemann surface of log z without crossing the sheet boundary. The lift starts at ln(π) + 0i or ln(π) + 2πi and ends at a point with imaginary part strictly between these, hence the bounds.

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

- `SlitPath` bundles the hypotheses: γ starts at π, γ(t) ∉ [0,∞) for t > 0, γ is continuous and piecewise smooth, and γ never hits 0. The "avoids nonneg real" condition is `¬(im = 0 ∧ re ≥ 0)`, which is `γ(t) ∉ [0,∞)` embedded in ℂ.
- `logIntegral γ` is defined as `∫ t in [0,1], γ'(t)/γ(t) dt` — the standard contour integral of dz/z.
- `arg_star` is the argument function with range (0, 2π), continuous on ℂ \ [0,∞). This differs from Mathlib's `Complex.arg` which has range (-π, π].
- The proof hinges on whether γ initially enters the upper or lower half-plane (determining the limiting value of arg\_\* at t = 0⁺), combined with `arg_star_endpoint_bounds` (γ(1) ∈ Ω implies strict bounds on arg\_\*(γ(1))).
- `limUnder (𝓝[>] 0) f` is the limit of f along the right-neighborhood filter of 0 — the one-sided limit as t → 0⁺.
