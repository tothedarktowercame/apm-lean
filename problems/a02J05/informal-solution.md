

# APM a02J05: The Dirichlet integral ∫ sin(x)/x dx = π

## Why It's Hard

The integrand sin(x)/x is not absolutely integrable (∫|sin x/x| dx = ∞), so the integral exists only as an improper Riemann integral (or principal value), not as a Lebesgue integral. You can't apply the residue theorem directly to sin(z)/z because sin(z) grows exponentially in the imaginary direction. The standard trick — replacing sin(x) by Im(e^{ix}) — introduces a function e^{iz}/z that decays in the upper half-plane, but has a pole at z = 0 that sits exactly on the real axis. Handling this pole requires an indented contour.

## The Key Insight

Consider f(z) = e^{iz}/z instead of sin(z)/z. Then Im f(x) = sin(x)/x for real x ≠ 0, and |e^{iz}| = e^{-Im z} → 0 in the upper half-plane, making the large semicircular arc vanish. The pole at z = 0 is on the contour, so indent around it with a small semicircle of radius ε. The residue contribution from the small semicircle gives -πi · Res(f, 0) = -πi (half the full residue, with a sign from the clockwise orientation). The rest gives ∫\_{-∞}^{∞} e^{ix}/x dx = πi, and taking the imaginary part: ∫ sin(x)/x dx = π.

## Complete Proof

**Theorem.** ∫\_{-∞}^{∞} sin(x)/x dx = π.

**Proof.**

**Step 1: Set up the contour.** Consider f(z) = e^{iz}/z. Define the contour γ consisting of four pieces:

- γ₁: real axis from -R to -ε
- γ₂: small semicircle C\_ε from -ε to ε in the upper half-plane (radius ε, traversed clockwise, i.e., from -ε to ε going through iε)
- γ₃: real axis from ε to R
- γ₄: large semicircle C\_R from R to -R in the upper half-plane (radius R, counterclockwise)

The contour γ = γ₁ + γ₂ + γ₃ + γ₄ is closed and f is analytic inside γ (no singularities — the pole at 0 is outside, having been indented around). By Cauchy's theorem:

$$\int_{\gamma_1} + \int_{\gamma_2} + \int_{\gamma_3} + \int_{\gamma_4} = 0.$$

**Step 2: The real line integrals (γ₁ + γ₃).**

$$\int_{\gamma_1} + \int_{\gamma_3} = \int_{-R}^{-\varepsilon}\frac{e^{ix}}{x}\,dx + \int_{\varepsilon}^{R}\frac{e^{ix}}{x}\,dx.$$

As ε → 0 and R → ∞, this becomes the principal value ∫\_{-∞}^{∞} e^{ix}/x dx (PV).

**Step 3: The large semicircle (γ₄) vanishes.**

Parametrise z = Re^{iθ}, θ from 0 to π:

$$\left|\int_{\gamma_4}\frac{e^{iz}}{z}\,dz\right| \leq \int_0^{\pi}\frac{e^{-R\sin\theta}}{R}\cdot R\,d\theta = \int_0^{\pi} e^{-R\sin\theta}\,d\theta.$$

By Jordan's lemma (using sin θ ≥ 2θ/π for θ ∈ [0, π/2]):

$$\int_0^{\pi} e^{-R\sin\theta}\,d\theta \leq 2\int_0^{\pi/2} e^{-2R\theta/\pi}\,d\theta = 2\cdot\frac{\pi}{2R}(1-e^{-R}) \leq \frac{\pi}{R} \to 0.$$

**Step 4: The small semicircle (γ₂) gives -πi.**

Parametrise z = εe^{iθ}, θ from π to 0 (clockwise):

$$\int_{\gamma_2}\frac{e^{iz}}{z}\,dz = \int_{\pi}^{0}\frac{e^{i\varepsilon e^{i\theta}}}{\varepsilon e^{i\theta}}\cdot i\varepsilon e^{i\theta}\,d\theta = i\int_{\pi}^{0} e^{i\varepsilon e^{i\theta}}\,d\theta = -i\int_0^{\pi} e^{i\varepsilon e^{i\theta}}\,d\theta.$$

As ε → 0, e^{iε e^{iθ}} → 1 uniformly, so:

$$\int_{\gamma_2}\frac{e^{iz}}{z}\,dz \to -i\int_0^{\pi}1\,d\theta = -i\pi.$$

**Step 5: Combine.**

Taking ε → 0 and R → ∞:

$$\text{PV}\int_{-\infty}^{\infty}\frac{e^{ix}}{x}\,dx + (-i\pi) + 0 = 0.$$

Therefore:

$$\text{PV}\int_{-\infty}^{\infty}\frac{e^{ix}}{x}\,dx = i\pi.$$

**Step 6: Extract the real and imaginary parts.**

$$\text{PV}\int_{-\infty}^{\infty}\frac{e^{ix}}{x}\,dx = \text{PV}\int_{-\infty}^{\infty}\frac{\cos x}{x}\,dx + i\,\text{PV}\int_{-\infty}^{\infty}\frac{\sin x}{x}\,dx.$$

The real part: cos(x)/x is an odd function, so PV∫ cos(x)/x dx = 0.

The imaginary part: sin(x)/x is an even function, so PV∫ sin(x)/x dx = 2∫₀^∞ sin(x)/x dx. But also PV∫ sin(x)/x dx = ∫\_{-∞}^{∞} sin(x)/x dx (the integrand has no singularity at 0, since sin(x)/x → 1).

Equating imaginary parts:

$$\int_{-\infty}^{\infty}\frac{\sin x}{x}\,dx = \pi. \qquad \blacksquare$$

## What Connects

**To Jordan's lemma.** The vanishing of the large arc integral is the classic application of Jordan's lemma. It works for any f(z) = g(z)e^{iaz} with a > 0 and g → 0 on the large semicircle.

**To the theory of distributions.** PV(1/x) is a tempered distribution, and its Fourier transform is -iπ sgn(ξ). The identity PV∫ e^{ix}/x dx = iπ is the Fourier transform of PV(1/x) evaluated at ξ = 1.

**To the Dirichlet kernel.** The integral ∫₀^∞ sin(x)/x dx = π/2 appears as the limiting case of ∫₀^∞ sin(Nx)/x dx = π/2 for all N > 0, which underlies the convergence of Fourier series (the Dirichlet integral is the normalization of the Dirichlet kernel).

**To the Laplace/Fourier transform.** Im∫₀^∞ e^{(i-s)x}/x dx (with regularisation) gives arctan(1/s), and as s → 0⁺, arctan(1/s) → π/2. This is the Laplace-transform proof of ∫₀^∞ sin(x)/x dx = π/2.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Order.Filter.Basic

open Complex Real Set Filter MeasureTheory

noncomputable section

/-- The Dirichlet integral: ∫_{-∞}^{∞} sin(x)/x dx = π.
    Stated as a limit of integrals over [-R, -ε] ∪ [ε, R]
    since sin(x)/x is not absolutely integrable. -/
theorem dirichlet_integral :
    Tendsto
      (fun R : ℝ => ∫ x in Icc (-R) R, Real.sin x / x)
      atTop (𝓝 Real.pi) := by
  sorry

/-- Half-line version: ∫₀^∞ sin(x)/x dx = π/2. -/
theorem dirichlet_integral_half :
    Tendsto
      (fun R : ℝ => ∫ x in Ioc 0 R, Real.sin x / x)
      atTop (𝓝 (Real.pi / 2)) := by
  sorry

/-- Jordan's lemma: the large semicircular arc integral vanishes.
    ∫_{C_R} e^{iz}/z dz → 0 as R → ∞. -/
lemma jordan_arc_vanishes :
    Tendsto (fun R : ℝ =>
      ‖∮ z in C(0, R), fun z => exp (I * z) / z‖)
      atTop (𝓝 0) := by
  sorry

/-- The standard Jordan bound:
    ∫₀^π e^{-R sin θ} dθ ≤ π/R for R > 0. -/
lemma jordan_bound {R : ℝ} (hR : 0 < R) :
    ∫ θ in Icc 0 Real.pi, Real.exp (-R * Real.sin θ) ≤ Real.pi / R := by
  sorry

/-- The small semicircle integral: the indentation around z = 0
    contributes -iπ in the limit ε → 0.
    ∫_{C_ε, clockwise} e^{iz}/z dz → -iπ. -/
lemma small_semicircle_limit :
    Tendsto (fun ε : ℝ =>
      -I * ∫ θ in Icc 0 Real.pi,
        exp (I * ε * exp (I * θ)))
      (𝓝[>] 0) (𝓝 (-I * Real.pi)) := by
  sorry

/-- The principal value integral: PV ∫ e^{ix}/x dx = iπ.
    This combines the real-axis integrals with the arc limits. -/
theorem principal_value_exp_over_x :
    Tendsto (fun p : ℝ × ℝ =>
      ∫ x in Icc (-p.1) (-p.2), exp (I * x) / x +
      ∫ x in Icc p.2 p.1, exp (I * x) / x)
      (atTop ×ˢ 𝓝[>] 0) (𝓝 (I * Real.pi)) := by
  sorry

/-- Cauchy's theorem: no singularity inside the indented contour,
    so the total contour integral is zero. -/
lemma indented_contour_zero
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (hεR : ε < R) :
    (∫ x in Icc (-R) (-ε), exp (I * x) / x) +
    (-I * ∫ θ in Icc 0 Real.pi, exp (I * ε * exp (I * θ))) +
    (∫ x in Icc ε R, exp (I * x) / x) +
    (I * R * ∫ θ in Icc 0 Real.pi,
      exp (I * R * exp (I * θ)) / (R * exp (I * θ)) *
        exp (I * θ)) = 0 := by
  sorry

/-- sin(x)/x has a removable singularity at 0 with value 1. -/
lemma sinc_continuous : Continuous (fun x : ℝ =>
    if x = 0 then 1 else Real.sin x / x) := by
  sorry

/-- cos(x)/x is odd, so its principal value integral is 0. -/
lemma pv_cos_over_x_eq_zero :
    ∀ R ε : ℝ, 0 < ε → ε < R →
      ∫ x in Icc (-R) (-ε), Real.cos x / x +
      ∫ x in Icc ε R, Real.cos x / x = 0 := by
  sorry

end
```

**Mathlib notes:**

- The Dirichlet integral is stated as a limit: `Tendsto (fun R => ∫ x in Icc (-R) R, sin x / x) atTop (𝓝 π)` since sin(x)/x is not in L¹ and the integral is an improper Riemann integral.
- The principal value integral uses the product filter `atTop ×ˢ 𝓝[>] 0` to take R → ∞ and ε → 0⁺ simultaneously (or sequentially — the result is independent of the order).
- `∮ z in C(0, R), f z` denotes `circleIntegral` from Mathlib. The Jordan lemma bound applies to this.
- `I * ∫ θ in Icc 0 π, exp(I * ε * exp(I * θ))` parametrises the small semicircle integral after the change of variables z = εe^{iθ}.
- `sinc_continuous` establishes that sin(x)/x extends continuously to x = 0 (with value 1), so the full-line integral ∫\_{-R}^{R} sin(x)/x dx is an ordinary Riemann integral (no principal value needed for the integrand itself — only for e^{ix}/x).
- `pv_cos_over_x_eq_zero` uses the oddness of cos(x)/x to extract the imaginary part from the complex integral.
