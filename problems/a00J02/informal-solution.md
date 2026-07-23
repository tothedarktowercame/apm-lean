

# APM a00J02: Decay rate of an absolutely continuous function with L^2 derivative

## Why It's Hard

You're given a function f with f(0) = 0 and f' ∈ L^2, and you need to find the exact asymptotic rate at which f(x) vanishes near 0. The claim is that x^{-1/2} f(x) → 0, meaning f vanishes *faster* than √x. This is not obvious: absolutely continuous functions with f(0) = 0 can grow as fast as x near 0 (if f' is bounded) or slower (if f' vanishes), but the L^2 integrability of f' forces a precise rate. The challenge is extracting a pointwise asymptotic from an integral condition on the derivative.

## The Key Insight

Use the fundamental theorem of calculus to write f(x) = ∫₀ˣ f'(t) dt, then apply Cauchy-Schwarz:

|f(x)| = |∫₀ˣ f'(t) · 1 dt| ≤ (∫₀ˣ |f'(t)|² dt)^{1/2} · (∫₀ˣ 1² dt)^{1/2} = √x · (∫₀ˣ |f'|² dt)^{1/2}

So |x^{-1/2} f(x)| ≤ (∫₀ˣ |f'|² dt)^{1/2}, and this → 0 as x → 0⁺ because f' ∈ L^2 and the integral over a shrinking interval vanishes. The limit is **0**.

## Complete Proof

**Theorem.** Let f : [0,1] → ℝ be absolutely continuous with f(0) = 0 and ∫₀¹ |f'(x)|² dx < ∞. Then lim_{x→0⁺} x^{-1/2} f(x) = 0.

**Proof.**

Since f is absolutely continuous on [0,1] with f(0) = 0, the fundamental theorem of calculus gives

$$f(x) = \int_0^x f'(t) \, dt \quad \text{for all } x \in [0,1].$$

By Cauchy-Schwarz applied to the functions f'(t) and 1 on the interval [0,x]:

$$|f(x)| = \left|\int_0^x f'(t) \, dt\right| \leq \left(\int_0^x |f'(t)|^2 \, dt\right)^{1/2} \cdot \left(\int_0^x 1 \, dt\right)^{1/2} = \sqrt{x} \cdot \left(\int_0^x |f'(t)|^2 \, dt\right)^{1/2}.$$

Dividing both sides by √x (for x > 0):

$$\left|\frac{f(x)}{\sqrt{x}}\right| \leq \left(\int_0^x |f'(t)|^2 \, dt\right)^{1/2}.$$

Now define g(x) = ∫₀ˣ |f'(t)|² dt. Since |f'|² is integrable on [0,1] (by hypothesis), g is the indefinite integral of a nonneg integrable function. By the fundamental property of the Lebesgue integral:

$$\lim_{x \to 0^+} g(x) = \lim_{x \to 0^+} \int_0^x |f'(t)|^2 \, dt = 0.$$

This holds because f' ∈ L^2 implies |f'|² ∈ L^1, and the integral of an L^1 function over a set of vanishing measure goes to zero (absolute continuity of the Lebesgue integral).

Therefore:

$$0 \leq \left|\frac{f(x)}{\sqrt{x}}\right| \leq \left(\int_0^x |f'(t)|^2 \, dt\right)^{1/2} \to 0 \quad \text{as } x \to 0^+.$$

By the squeeze theorem, lim_{x→0⁺} x^{-1/2} f(x) = 0. ∎

**Remark on sharpness.** The exponent 1/2 is sharp. If f'(t) = t^{-α} for α < 1/2 (so that f' ∈ L^2 near 0), then f(x) ~ x^{1-α}/(1-α), and x^{-1/2} f(x) ~ x^{1/2 - α} → 0. But if f'(t) = t^{-1/2} (borderline, f' ∉ L^2), then f(x) = 2√x and x^{-1/2} f(x) = 2 ≠ 0. The L^2 condition on f' is exactly what buys the extra decay.

## What Connects

**To Sobolev embeddings.** This is the one-dimensional Sobolev embedding W^{1,2}(0,1) ↪ C^{0,1/2}([0,1]) — functions with L^2 derivatives are 1/2-Hölder continuous. The estimate |f(x) - f(y)| ≤ ||f'||_{L^2} · |x-y|^{1/2} is exactly our Cauchy-Schwarz bound with f(y) = 0. This problem asks you to prove the *vanishing* version: not just |f(x)| ≤ C√x but x^{-1/2}f(x) → 0, which requires the absolute continuity of the integral (the C depends on the L^2 norm *on [0,x]*, which shrinks).

**To Hardy's inequality.** The estimate can be strengthened: ∫₀¹ |f(x)/√x|² dx ≤ 4 ∫₀¹ |f'(x)|² dx (Hardy's inequality with exponent p=2). Our pointwise limit result is weaker than this but uses the same mechanism.

**To the Cauchy-Schwarz trick.** Writing an integral ∫ f' · 1 and applying C-S to separate the derivative from the geometry is a core technique in PDE regularity theory (Morrey's inequality, De Giorgi estimates).

---

## Lean 4 Theorem Statements

```lean
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic

open MeasureTheory Filter Set

noncomputable section

/-- Cauchy-Schwarz for integrals on [0,x]:
    |∫₀ˣ f'(t) dt| ≤ √x · (∫₀ˣ |f'(t)|² dt)^{1/2} -/
lemma integral_le_sqrt_mul_L2norm
    {f' : ℝ → ℝ} (hf' : IntegrableOn f' (Icc 0 1) volume)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖∫ t in Icc 0 x, f' t‖ ≤
      Real.sqrt x * Real.sqrt (∫ t in Icc 0 x, ‖f' t‖ ^ 2) := by
  sorry

/-- Absolute continuity of the Lebesgue integral:
    ∫₀ˣ |f'|² dt → 0 as x → 0⁺ when f' ∈ L². -/
lemma tendsto_set_integral_Icc_zero
    {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 1) volume) :
    Tendsto (fun x => ∫ t in Icc 0 x, g t ∂volume)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Corollary: (∫₀ˣ |f'|² dt)^{1/2} → 0 as x → 0⁺. -/
lemma tendsto_sqrt_set_integral_sq
    {f' : ℝ → ℝ} (hf'sq : IntegrableOn (fun t => ‖f' t‖ ^ 2) (Icc 0 1) volume) :
    Tendsto (fun x => Real.sqrt (∫ t in Icc 0 x, ‖f' t‖ ^ 2 ∂volume))
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Main theorem: x⁻¹/² f(x) → 0 as x → 0⁺.

    Hypotheses:
    - f is absolutely continuous on [0,1] (expressed as the integral of its derivative)
    - f(0) = 0
    - f' ∈ L²([0,1])

    We express f via FTC: f(x) = ∫₀ˣ f'(t) dt. -/
theorem tendsto_div_sqrt_zero
    {f f' : ℝ → ℝ}
    (hf_ac : ∀ x ∈ Icc (0 : ℝ) 1,
      f x = f 0 + ∫ t in Icc 0 x, f' t ∂volume)
    (hf0 : f 0 = 0)
    (hf' : IntegrableOn f' (Icc 0 1) volume)
    (hf'_sq : IntegrableOn (fun t => ‖f' t‖ ^ 2) (Icc 0 1) volume) :
    Tendsto (fun x => f x / Real.sqrt x)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Equivalent statement using x^(-1/2) · f(x) notation. -/
theorem tendsto_rpow_neg_half_mul_zero
    {f f' : ℝ → ℝ}
    (hf_ac : ∀ x ∈ Icc (0 : ℝ) 1,
      f x = ∫ t in Icc 0 x, f' t ∂volume)
    (hf' : IntegrableOn f' (Icc 0 1) volume)
    (hf'_sq : IntegrableOn (fun t => ‖f' t‖ ^ 2) (Icc 0 1) volume) :
    Tendsto (fun x => x ^ (-(1 : ℝ) / 2) * f x)
      (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- The bound that drives the proof:
    |f(x)/√x| ≤ (∫₀ˣ |f'|² dt)^{1/2} for x > 0. -/
lemma div_sqrt_le_L2_tail
    {f f' : ℝ → ℝ}
    (hf_ac : ∀ x ∈ Icc (0 : ℝ) 1,
      f x = ∫ t in Icc 0 x, f' t ∂volume)
    (hf' : IntegrableOn f' (Icc 0 1) volume)
    {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    ‖f x / Real.sqrt x‖ ≤
      Real.sqrt (∫ t in Icc 0 x, ‖f' t‖ ^ 2 ∂volume) := by
  sorry

end
```

**Mathlib notes:**

- `IntegrableOn f' (Icc 0 1) volume` expresses f' ∈ L^1([0,1]); the separate `hf'_sq` hypothesis gives f' ∈ L^2.
- The absolute continuity condition is expressed via FTC: f(x) = ∫₀ˣ f' dt. Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt` goes the other direction (from differentiability to the integral formula); here we take the integral representation as hypothesis.
- `𝓝[>] 0` is the right-neighborhood filter (`nhdsWithin 0 (Ioi 0)`), the natural filter for x → 0⁺.
- `Real.sqrt` is preferred over `rpow` for the √x factor since it's definitionally nonneg and has cleaner Mathlib API.
- The core bound `div_sqrt_le_L2_tail` is the Cauchy-Schwarz step after dividing by √x; the main theorem follows by squeezing this with `tendsto_sqrt_set_integral_sq`.