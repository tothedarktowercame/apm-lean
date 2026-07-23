

# APM a01A10: Fresnel integral and Fourier transform of the Gaussian

I'll compute both.

## Why It's Hard

**(a)** The integrand e^{ix²} has modulus 1 everywhere — it doesn't decay. The integral converges only by cancellation (oscillation), not by absolute integrability. You can't just apply the residue theorem to a closed contour; you need a contour that deforms the oscillatory integral into a Gaussian one.

**(b)** The integrand e^{ixy} e^{-x²} does decay, but computing the integral requires "completing the square" in the exponent, which shifts the contour of integration into the complex plane. Justifying this shift is the nontrivial step.

## The Key Insight

**(a)** Use the contour that is a *pie slice* of angle π/4 in the first quadrant. Along the real axis you get ∫₀^R e^{ix²} dx. Along the ray at angle π/4, parametrize z = te^{iπ/4} and get a Gaussian integral. The circular arc contributes nothing as R → ∞. Equating gives the Fresnel integral in terms of the known Gaussian ∫₀^∞ e^{-t²} dt = √π/2.

**(b)** The exponent is -x² + ixy = -(x - iy/2)² - y²/4. Substitute w = x - iy/2 (shift the contour vertically by -y/2 in the complex plane). The shifted integral is e^{-y²/4} ∫ e^{-w²} dw = √π e^{-y²/4}. Justify the contour shift by showing the contributions on vertical segments vanish.

## Complete Proof

### Part (a): ∫₀^∞ e^{ix²} dx = (1+i)√π / (2√2)

**Contour.** Let γ\_R be the boundary of the sector {z : 0 < arg z < π/4, |z| < R}, traversed counterclockwise. This consists of three pieces:

- γ₁: the real segment [0, R]
- γ₂: the circular arc from R to Re^{iπ/4}
- γ₃: the ray segment from Re^{iπ/4} back to 0

The function f(z) = e^{iz²} is entire, so ∮\_{γ\_R} e^{iz²} dz = 0 by Cauchy's theorem:

$$\int_{\gamma_1} + \int_{\gamma_2} + \int_{\gamma_3} = 0.$$

**γ₁ (real axis):**

$$\int_{\gamma_1} e^{iz^2}\,dz = \int_0^R e^{ix^2}\,dx.$$

**γ₃ (ray at angle π/4, traversed inward):** Parametrize z = te^{iπ/4} with t from R to 0, dz = e^{iπ/4} dt:

$$\int_{\gamma_3} e^{iz^2}\,dz = \int_R^0 e^{i(te^{i\pi/4})^2} e^{i\pi/4}\,dt = -e^{i\pi/4}\int_0^R e^{it^2 e^{i\pi/2}}\,dt.$$

Now e^{iπ/2} = i, so it² · i = it² · i = -t² (wait: i · t² · e^{iπ/2} — let me recompute). We have z² = t² e^{iπ/2} = it², so iz² = i · it² = -t². Therefore:

$$\int_{\gamma_3} = -e^{i\pi/4}\int_0^R e^{-t^2}\,dt.$$

**γ₂ (circular arc):** Parametrize z = Re^{iθ}, θ from 0 to π/4:

$$\left|\int_{\gamma_2} e^{iz^2}\,dz\right| \leq \int_0^{\pi/4} |e^{iR^2 e^{2i\theta}}| \cdot R\,d\theta = \int_0^{\pi/4} e^{-R^2\sin 2\theta} \cdot R\,d\theta.$$

By Jordan's inequality, sin 2θ ≥ 4θ/π for θ ∈ [0, π/4]:

$$\leq \int_0^{\pi/4} R e^{-R^2 \cdot 4\theta/\pi}\,d\theta = R \cdot \frac{\pi}{4R^2}(1 - e^{-R^2}) \leq \frac{\pi}{4R} \to 0.$$

**Combining:** As R → ∞:

$$\int_0^{\infty} e^{ix^2}\,dx - e^{i\pi/4}\int_0^{\infty} e^{-t^2}\,dt = 0.$$

Since ∫₀^∞ e^{-t²} dt = √π/2:

$$\int_0^{\infty} e^{ix^2}\,dx = e^{i\pi/4} \cdot \frac{\sqrt{\pi}}{2} = \frac{1+i}{\sqrt{2}} \cdot \frac{\sqrt{\pi}}{2} = \frac{(1+i)\sqrt{\pi}}{2\sqrt{2}}.$$

$$\boxed{\int_0^{\infty} e^{ix^2}\,dx = \frac{\sqrt{\pi}}{2}\,e^{i\pi/4} = \frac{(1+i)\sqrt{\pi}}{2\sqrt{2}} = \frac{\sqrt{2\pi}}{4}(1+i).} \qquad \blacksquare$$

### Part (b): ∫\_{-∞}^{∞} e^{ixy} e^{-x²} dx = √π e^{-y²/4}

**Completing the square.** The exponent is:

$$-x^2 + ixy = -\left(x - \frac{iy}{2}\right)^2 - \frac{y^2}{4}.$$

So the integral becomes:

$$e^{-y^2/4}\int_{-\infty}^{\infty} e^{-(x - iy/2)^2}\,dx.$$

**Contour shift.** We claim ∫\_{-∞}^{∞} e^{-(x-iy/2)²} dx = ∫\_{-∞}^{∞} e^{-w²} dw = √π.

To justify, consider the rectangular contour with vertices -R, R, R - iy/2, -R - iy/2, traversed counterclockwise. The function g(z) = e^{-z²} is entire, so ∮ g = 0.

The four sides:
- **Bottom** (from -R to R along ℝ): ∫\_{-R}^{R} e^{-x²} dx → √π.
- **Top** (from R - iy/2 to -R - iy/2, i.e., rightward): -∫\_{-R}^{R} e^{-(x-iy/2)²} dx.
- **Right side** (from R to R - iy/2): ∫₀^{y/2} e^{-(R-is)²} · (-i) ds. The modulus is bounded by (y/2) · e^{-R² + y²/4} → 0 as R → ∞.
- **Left side** (from -R - iy/2 to -R): similarly → 0.

So as R → ∞:

$$\int_{-\infty}^{\infty} e^{-x^2}\,dx - \int_{-\infty}^{\infty} e^{-(x-iy/2)^2}\,dx = 0.$$

Therefore:

$$\int_{-\infty}^{\infty} e^{ixy} e^{-x^2}\,dx = e^{-y^2/4}\int_{-\infty}^{\infty} e^{-w^2}\,dw = \sqrt{\pi}\,e^{-y^2/4}.$$

$$\boxed{\int_{-\infty}^{\infty} e^{ixy-x^2}\,dx = \sqrt{\pi}\,e^{-y^2/4}.} \qquad \blacksquare$$

## What Connects

**The Gaussian is its own Fourier transform.** Part (b) proves f̂(y) = √π e^{-y²/4} where f(x) = e^{-x²}. With proper normalisation, the Gaussian is an eigenfunction of the Fourier transform — the only L² function (up to scaling) that is invariant under Fourier transform.

**Fresnel integrals and diffraction.** Part (a) gives the Fresnel integral, fundamental in wave optics. The spiral traced by ∫₀^R e^{ix²} dx as R grows is the Cornu spiral, used to compute diffraction patterns at edges.

**Contour rotation vs contour shift.** Part (a) uses a rotation (the pie-slice at angle π/4 maps the oscillatory e^{ix²} to the decaying e^{-t²}). Part (b) uses a translation (shifting the contour by iy/2 completes the square). Both exploit the fact that e^{-z²} is entire, so contours can be deformed freely.

**Stationary phase.** The Fresnel integral is the simplest example of the stationary phase principle: the main contribution to ∫ e^{iλφ(x)} dx comes from the neighbourhood of critical points of φ. Here φ(x) = x², with a single critical point at x = 0.

---

## Lean 4 Theorem Statements

```lean
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory Complex Real Set Filter

noncomputable section

/-- Part (a): The Fresnel integral.
    ∫₀^∞ e^{ix²} dx = √π/2 · e^{iπ/4}. -/
theorem fresnel_integral :
    Tendsto (fun R : ℝ => ∫ x in Icc 0 R,
      Complex.exp (I * (x : ℂ) ^ 2))
      atTop (𝓝 (Real.sqrt π / 2 * Complex.exp (I * π / 4))) := by
  sorry

/-- Real and imaginary parts of the Fresnel integral:
    ∫₀^∞ cos(x²) dx = ∫₀^∞ sin(x²) dx = √(2π)/4. -/
theorem fresnel_cos :
    Tendsto (fun R : ℝ => ∫ x in Icc 0 R, Real.cos (x ^ 2))
      atTop (𝓝 (Real.sqrt (2 * π) / 4)) := by
  sorry

theorem fresnel_sin :
    Tendsto (fun R : ℝ => ∫ x in Icc 0 R, Real.sin (x ^ 2))
      atTop (𝓝 (Real.sqrt (2 * π) / 4)) := by
  sorry

/-- The arc integral vanishes: the contribution from the circular
    arc of radius R at angle π/4 tends to 0. -/
lemma fresnel_arc_vanishes :
    Tendsto (fun R : ℝ =>
      ‖∫ θ in Icc 0 (π / 4),
        Complex.exp (I * (R * Complex.exp (I * θ)) ^ 2) *
          (I * R * Complex.exp (I * θ))‖)
      atTop (𝓝 0) := by
  sorry

/-- The ray integral at angle π/4 gives the Gaussian:
    ∫₀^R e^{-t²} dt along z = te^{iπ/4}. -/
lemma fresnel_ray_eq_gaussian (R : ℝ) (hR : 0 < R) :
    ∫ t in Icc 0 R,
      Complex.exp (I * (t * Complex.exp (I * π / 4)) ^ 2) *
        Complex.exp (I * π / 4) =
    Complex.exp (I * π / 4) * ∫ t in Icc 0 R,
      Complex.exp (-(t : ℂ) ^ 2) := by
  sorry

/-- Part (b): Fourier transform of the Gaussian.
    ∫_{-∞}^{∞} e^{ixy} e^{-x²} dx = √π · e^{-y²/4}. -/
theorem fourier_gaussian (y : ℝ) :
    ∫ x : ℝ, Complex.exp (I * x * y) * Complex.exp (-(x : ℂ) ^ 2) =
      Real.sqrt π * Complex.exp (-(y : ℂ) ^ 2 / 4) := by
  sorry

/-- Completing the square: -x² + ixy = -(x - iy/2)² - y²/4. -/
lemma complete_square (x y : ℂ) :
    -x ^ 2 + I * x * y = -(x - I * y / 2) ^ 2 - y ^ 2 / 4 := by
  sorry

/-- Contour shift: ∫_{-∞}^∞ e^{-(x-ic)²} dx = ∫_{-∞}^∞ e^{-x²} dx
    for any real c, justified by a rectangular contour. -/
lemma integral_gaussian_shift (c : ℝ) :
    ∫ x : ℝ, Complex.exp (-((x : ℂ) - I * c) ^ 2) =
      ∫ x : ℝ, Complex.exp (-(x : ℂ) ^ 2) := by
  sorry

/-- The vertical sides of the rectangular contour vanish. -/
lemma rectangular_sides_vanish (c : ℝ) :
    Tendsto (fun R : ℝ =>
      ‖∫ s in Icc 0 c,
        Complex.exp (-((R : ℂ) - I * s) ^ 2) * (-I)‖)
      atTop (𝓝 0) := by
  sorry

/-- The standard Gaussian integral: ∫_{-∞}^∞ e^{-x²} dx = √π.
    This is in Mathlib as `integral_gaussian`. -/
lemma gaussian_integral_eq :
    ∫ x : ℝ, Real.exp (-(x ^ 2)) = Real.sqrt π := by
  sorry

end
```

**Mathlib notes:**

- `integral_gaussian` in Mathlib (`Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`) already proves ∫ e^{-bx²} = √(π/b). Part (b) reduces to this via the contour shift.
- The Fresnel integral is stated as a limit of integrals over [0,R] rather than an improper integral, since the integrand is not absolutely integrable — `Tendsto ... atTop (𝓝 value)` is the natural Lean encoding.
- `Complex.exp (I * (x:ℂ)^2)` is e^{ix²}. The coercion `(x : ℂ)` embeds ℝ into ℂ.
- `complete_square` is pure algebra (ring computation). In Lean this could be closed by `ring` once the types align.
- The contour shift `integral_gaussian_shift` is the core analytic step. The vertical sides lemma `rectangular_sides_vanish` provides the justification — `e^{-(R-is)²}` decays as e^{-R²} for fixed s.
- Part (b)'s result is essentially `MeasureTheory.integral_comp_mul_right` composed with `integral_gaussian` after the contour shift, plus the `complete_square` algebraic identity.
