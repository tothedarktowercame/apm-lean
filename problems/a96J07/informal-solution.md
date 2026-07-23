

## 1. Informal proof

**Why it's hard:** The problem has two parts — a contour integral evaluation requiring partial fractions when a ≠ b, and then a non-obvious leap to Liouville's theorem. The connection between the integral formula and boundedness implying constancy isn't immediate; you need to see how to exploit the freedom to let R → ∞.

**The key insight:** Partial fractions decompose the integrand into two Cauchy kernel terms, each evaluated by Cauchy's integral formula. The resulting expression f(a)/(a-b) - f(b)/(a-b) = (f(a)-f(b))/(a-b) relates the contour integral to a difference quotient. If f is bounded, the ML estimate forces the integral to 0 as R → ∞, so f(a) = f(b) for all a, b — hence f is constant.

**Proof:**

*Part 1: Evaluate the integral.*

Assume a ≠ b with |a| < R and |b| < R. By partial fractions:

$$\frac{1}{(z-a)(z-b)} = \frac{1}{a-b}\left(\frac{1}{z-a} - \frac{1}{z-b}\right)$$

Therefore:

$$\int_\gamma \frac{f(z)}{(z-a)(z-b)}\,dz = \frac{1}{a-b}\left(\int_\gamma \frac{f(z)}{z-a}\,dz - \int_\gamma \frac{f(z)}{z-b}\,dz\right)$$

Since f is entire and γ is the circle of radius R centered at 0, with both a and b inside the circle (|a| < R, |b| < R), Cauchy's integral formula gives:

$$\int_\gamma \frac{f(z)}{z-a}\,dz = 2\pi i\, f(a), \qquad \int_\gamma \frac{f(z)}{z-b}\,dz = 2\pi i\, f(b)$$

So:

$$\int_\gamma \frac{f(z)}{(z-a)(z-b)}\,dz = \frac{2\pi i\,(f(a) - f(b))}{a - b}$$

*Part 2: Liouville's theorem.*

Suppose f is entire and bounded, say |f(z)| ≤ M for all z ∈ ℂ. Fix any two distinct points a, b ∈ ℂ. Choose R > max(|a|, |b|) so that both points lie inside γ.

Estimate the integral directly using the ML inequality. On γ, |z| = R, so:

$$|z - a| \geq R - |a|, \qquad |z - b| \geq R - |b|$$

The length of γ is 2πR, so:

$$\left|\int_\gamma \frac{f(z)}{(z-a)(z-b)}\,dz\right| \leq \frac{M \cdot 2\pi R}{(R - |a|)(R - |b|)}$$

From Part 1, this equals:

$$\frac{2\pi |f(a) - f(b)|}{|a - b|}$$

Combining:

$$|f(a) - f(b)| \leq \frac{M \cdot R \cdot |a - b|}{(R - |a|)(R - |b|)}$$

As R → ∞, the right side tends to 0 (the numerator grows as R while the denominator grows as R²). Therefore f(a) = f(b). Since a and b were arbitrary, f is constant. ∎

**What connects:** This is a slick variant of the standard Cauchy-estimate proof of Liouville's theorem. Instead of bounding the derivative via Cauchy's formula for f', it bounds the difference quotient (f(a)-f(b))/(a-b) directly by evaluating a two-pole contour integral in two ways: exactly via partial fractions + Cauchy's formula, and in magnitude via the ML estimate. The decay is R/(R-|a|)(R-|b|) ~ 1/R → 0, which is the same rate that appears in the usual proof. The approach generalizes: replacing the two simple poles with a double pole at a single point recovers the derivative version.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex MeasureTheory Metric Set

noncomputable section

/-- Cauchy integral formula applied to f(z)/((z-a)(z-b)) via partial fractions:
    the contour integral equals 2πi(f(a) - f(b))/(a - b). -/
theorem apm_a96J07_contour_eval
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (a b : ℂ) (hab : a ≠ b)
    (R : ℝ) (hR : 0 < R) (haR : ‖a‖ < R) (hbR : ‖b‖ < R) :
    ∮ z in C(0, R), f z / ((z - a) * (z - b)) =
      2 * π * I * (f a - f b) / (a - b) := by sorry

/-- ML estimate: the contour integral is bounded by M · 2πR / ((R-|a|)(R-|b|)). -/
theorem apm_a96J07_ml_bound
    (f : ℂ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ M)
    (a b : ℂ) (hab : a ≠ b)
    (R : ℝ) (hR : 0 < R) (haR : ‖a‖ < R) (hbR : ‖b‖ < R) :
    ‖∮ z in C(0, R), f z / ((z - a) * (z - b))‖ ≤
      M * (2 * π * R) / ((R - ‖a‖) * (R - ‖b‖)) := by sorry

/-- Main result: Liouville's theorem via the two-pole contour integral.
    A bounded entire function is constant. -/
theorem apm_a96J07_liouville
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (M : ℝ) (hbound : ∀ z : ℂ, ‖f z‖ ≤ M) :
    ∀ a b : ℂ, f a = f b := by sorry

/-- Auxiliary: R / ((R - c₁)(R - c₂)) → 0 as R → ∞ for fixed c₁ c₂. -/
theorem apm_a96J07_decay
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    Filter.Tendsto (fun R : ℝ => R / ((R - c₁) * (R - c₂)))
      Filter.atTop (nhds 0) := by sorry
```

## 3. Mathlib cross-references

**Types/structures:**
- `ℂ` / `Complex` — the complex numbers
- `circleIntegral` / `∮ z in C(c, R)` — circle contour integral notation
- `Differentiable ℂ f` — entire function (differentiable on all of ℂ)
- `Filter.atTop` — filter for R → ∞
- `nhds` — neighborhood filter

**Key lemmas:**
- `Complex.circleIntegral_sub_inv_smul` — Cauchy integral formula: ∮ f(z)/(z-a) dz = 2πi f(a)
- `circleIntegral.norm_le` — ML estimate for circle integrals
- `norm_circleIntegral_le_of_norm_le_const` — bound ‖∮...‖ ≤ M · 2πR
- `DifferentiableOn.div` — f/g is differentiable where g ≠ 0
- `Differentiable.comp` — composition of differentiable functions
- `circleIntegral_div_sub` — relates ∮ f/(z-a) to winding number
- `Complex.norm_eq_abs` — ‖z‖ = |z| bridge
- `abs_sub_abs_le_abs_sub` — reverse triangle inequality ||z| - |a|| ≤ |z - a|
- `Filter.Tendsto.div_atTop` — tendsto 0 for quotients where denominator → ∞
- `tendsto_const_div_atTop_nhds_0_nat` / polynomial filter tendsto lemmas
- `eq_of_forall_dist_le` — if dist(f(a), f(b)) ≤ ε for all ε > 0 then f(a) = f(b)
- `Liouville.apply` / `Complex.liouville_theorem` — Mathlib's existing Liouville (for comparison)
- `norm_mul_le` — ‖a * b‖ ≤ ‖a‖ * ‖b‖
- `norm_div_le` — norm of quotient bound
- `mul_inv_cancel₀` — a - b ≠ 0 cancellation

**Tactic hints:**
- `field_simp` — clear denominators in the partial fraction identity
- `ring` — verify the partial fraction algebraic identity
- `nlinarith` — close R - |a| > 0, denominator positivity, and final decay estimate
- `positivity` — for 0 < R, 0 < R - ‖a‖, etc.
- `gcongr` — monotone inequality manipulation on the ML bound
- `simp [circleIntegral]` — unfold contour integral definitions
- `have : R - ‖a‖ > 0 := by linarith` — frequent positivity side goals
- `tendsto_nhds_unique` — if limit is both (f(a)-f(b))/(a-b) and 0, conclude equality
- `filter_upwards` — for eventually-type arguments when R is large enough