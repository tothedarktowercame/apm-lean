

# APM a94A06: $\int_{0}^\infty x^{7}/(1+x^{12})\, dx$ via pie-slice contour

## 1. Informal proof

**Why it's hard.** The integrand $x^{7}/(1+x^{12})$ is a rational function, but the degree 12 in the denominator means the poles are 12th roots of $-1$, distributed around the circle. A semicircular contour would enclose 6 poles — messy. The pie-slice trick exploits the rotational symmetry $x \mapsto xe^{i\pi/6}$ of $x^{12}$ to relate the integral along the ray at angle $\pi/6$ back to the original integral, avoiding multiple residue computations.

**The key insight.** On the ray $z = re^{i\pi/6}$, $z^{12} = r^{12}e^{2\pi i} = r^{12}$ and $z^{7} = r^{7}e^{7i\pi/6}$, so $z^{7}/(1+z^{12}) = e^{7i\pi/6} \cdot r^{7}/(1+r^{12})$. The integral along this ray is $e^{7i\pi/6} \cdot e^{i\pi/6} \cdot I = e^{8i\pi/6} \cdot I$ where $I$ is the original integral and the extra $e^{i\pi/6}$ comes from $dz = e^{i\pi/6}dr$. The contour integral equals the real-axis piece minus the ray piece (accounting for direction), and the arc at infinity vanishes.

**Proof.**

*Step 1: Contour.* Let $\gamma_R$ be the boundary of the pie-slice $\{z : 0 < \arg z < \pi/6, |z| < R\}$, traversed counterclockwise:
- $\gamma_{1}$: real axis from 0 to $R$
- $\gamma_{2}$: arc from $R$ to $Re^{i\pi/6}$
- $\gamma_{3}$: ray from $Re^{i\pi/6}$ back to 0

Consider $f(z) = z^{7}/(1+z^{12})$.

*Step 2: Poles inside the contour.* The poles of $f$ are the 12th roots of $-1$: $z_k = e^{i(2k+1)\pi/12}$ for $k = 0,\ldots,11$. In the sector $0 < \arg z < \pi/6 = \pi/6$, we need $0 < (2k+1)\pi/12 < \pi/6$, i.e., $0 < 2k+1 < 2$, so $k = 0$ only. The sole pole inside is $z_{0} = e^{i\pi/12}$.

*Step 3: Residue at $z_{0}$.* Since $1+z^{12}$ has simple roots: $\mathrm{Res}(f, z_{0}) = z_{0}^{7}/(12z_{0}^{11}) = 1/(12z_{0}^{4}) = e^{-4i\pi/12}/12 = e^{-i\pi/3}/12$.

*Step 4: Ray integral ($\gamma_{3}$).* Parametrise $z = re^{i\pi/6}$, $r$ from $R$ to 0, $dz = e^{i\pi/6}dr$:

$\int_{\gamma_{3}} = \int_R^0 (re^{i\pi/6})^{7}/(1+(re^{i\pi/6})^{12}) \cdot e^{i\pi/6}\, dr = -e^{8i\pi/6} \int_0^R r^{7}/(1+r^{12})\, dr$

since $(e^{i\pi/6})^{12} = e^{2\pi i} = 1$ and $(e^{i\pi/6})^{7} \cdot e^{i\pi/6} = e^{8i\pi/6}$.

*Step 5: Arc ($\gamma_{2}$) vanishes.* $|f(Re^{i\theta})| \leq R^{7}/(R^{12}-1) = O(R^{-5})$, and arc length $= \pi R/6$, so $|\int_{\gamma_{2}}| \leq O(R^{-4}) \to 0$.

*Step 6: Combine.* By the residue theorem:

$\int_{\gamma_{1}} + \int_{\gamma_{2}} + \int_{\gamma_{3}} = 2\pi i \cdot \mathrm{Res}(f, z_{0})$.

As $R \to \infty$: $I + 0 - e^{8i\pi/6} I = 2\pi i \cdot e^{-i\pi/3}/12$.

Now $e^{8i\pi/6} = e^{4i\pi/3} = \cos(4\pi/3) + i \sin(4\pi/3) = -1/2 - i\sqrt{3}/2$.

So $I(1 - e^{4i\pi/3}) = I(1+1/2+i\sqrt{3}/2) = I(3/2 + i\sqrt{3}/2)$.

And $2\pi i \cdot e^{-i\pi/3}/12 = (\pi i/6)(\cos(\pi/3) - i \sin(\pi/3)) = (\pi i/6)(1/2 - i\sqrt{3}/2) = (\pi/6)(\sqrt{3}/2 + i/2)$.

Equating real parts: $I \cdot 3/2 = \pi\sqrt{3}/12$, so $I = \pi\sqrt{3}/18 = \pi/(6\sqrt{3})$.

Simplifying: $I = \pi\sqrt{3}/18$.

$$\boxed{\int_0^\infty \frac{x^7}{1+x^{12}}\,dx = \frac{\pi\sqrt{3}}{18} = \frac{\pi}{6\sqrt{3}}.}$$

**What connects.** This is a standard application of the pie-slice (sector) contour for integrals $\int_{0}^\infty x^{a}/(1+x^{n})\, dx$ where the angle $\pi/n$ is chosen so that the substitution $z = re^{2\pi i/n}$ maps $z^n$ back to $r^n$, reducing the ray integral to a multiple of the original. The general formula is $\int_{0}^\infty x^{a}/(1+x^{n})\, dx = \pi/(n \sin((a+1)\pi/n))$ for $-1 < a < n-1$. Here $a = 7$, $n = 12$: $\pi/(12 \sin(8\pi/12)) = \pi/(12 \sin(2\pi/3)) = \pi/(12 \cdot \sqrt{3}/2) = \pi/(6\sqrt{3}) = \pi\sqrt{3}/18$. ✓

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral

open Real MeasureTheory Set

noncomputable section

/-- Main result: ∫₀^∞ x⁷/(1+x¹²) dx = π√3/18. -/
theorem integral_x7_over_1_plus_x12 :
    Tendsto (fun R => ∫ x in (0:ℝ)..R, x ^ 7 / (1 + x ^ 12))
      Filter.atTop (𝓝 (π * sqrt 3 / 18)) := by
  sorry

/-- The sole pole in the sector 0 < arg z < π/6 is e^{iπ/12}. -/
lemma pole_in_sector :
    ∀ z : ℂ, 1 + z ^ 12 = 0 → 0 < z.arg → z.arg < π / 6 →
      z = Complex.exp (Complex.I * (π / 12)) := by
  sorry

/-- Residue computation: Res(z⁷/(1+z¹²), e^{iπ/12}) = e^{-iπ/3}/12. -/
lemma residue_at_pole :
    let z₀ := Complex.exp (Complex.I * (↑(π / 12) : ℂ))
    z₀ ^ 7 / (12 * z₀ ^ 11) =
      Complex.exp (-(Complex.I * (↑(π / 3) : ℂ))) / 12 := by
  sorry

/-- The arc integral vanishes as R → ∞. -/
lemma arc_integral_vanishes :
    Tendsto (fun R : ℝ =>
      ‖∫ θ in (0:ℝ)..(π/6),
        (R * Complex.exp (Complex.I * θ)) ^ 7 /
        (1 + (R * Complex.exp (Complex.I * θ)) ^ 12) *
        Complex.I * R * Complex.exp (Complex.I * θ)‖)
      Filter.atTop (𝓝 0) := by
  sorry

/-- The ray integral equals e^{8iπ/6} times the real integral. -/
lemma ray_integral_factor (R : ℝ) (hR : 0 < R) :
    ∫ r in (0:ℝ)..R,
      (r * Complex.exp (Complex.I * (π/6))) ^ 7 /
      (1 + (r * Complex.exp (Complex.I * (π/6))) ^ 12) *
      Complex.exp (Complex.I * (π/6)) =
    Complex.exp (Complex.I * (8 * π / 6)) *
      ∫ r in (0:ℝ)..R, ↑(r ^ 7 / (1 + r ^ 12)) := by
  sorry

/-- General formula: ∫₀^∞ xᵃ/(1+xⁿ) = π/(n sin((a+1)π/n))
    for -1 < a < n-1. -/
theorem integral_xa_over_1_plus_xn
    {a : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (ha_low : -1 < a) (ha_high : a < ↑n - 1) :
    Tendsto (fun R => ∫ x in (0:ℝ)..R, x ^ a / (1 + x ^ (n : ℝ)))
      Filter.atTop (𝓝 (π / (↑n * sin ((a + 1) * π / ↑n)))) := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `Complex.exp`, `Complex.I` — complex exponential and imaginary unit
- `Complex.arg` — argument function
- `intervalIntegral` / `∫ x in a..b` — for the real integral
- `Filter.atTop` — for $R \to \infty$ (improper integral)
- `Real.sqrt`, `Real.sin`, `Real.pi` — for the answer

**Key lemmas:**
- `Complex.circleIntegral_sub_inv_of_mem_ball` — Cauchy integral / residue formula in Mathlib
- `Complex.exp_mul_I` — $e^{i\theta}$ computation
- `Complex.exp_nat_mul` — $(e^{i\alpha})^{n} = e^{in\alpha}$
- `Complex.norm_exp_ofReal_mul_I` — $|e^{i\theta}| = 1$
- `intervalIntegral.integral_comp_mul_right` — substitution for parametrising the ray
- `Real.rpow_natCast` — $x^n$ for real powers
- `norm_div_le` / `norm_pow` — for bounding the arc integrand
- `Real.sin_pi_div_three` — $\sin(\pi/3) = \sqrt{3}/2$
- `Real.cos_pi_div_three` — $\cos(\pi/3) = 1/2$
- `Real.sqrt_eq_iff_sq_eq` — for $\sqrt{3}$ manipulation

**Tactic hints:**
- `norm_num [Real.sin_pi_div_three, Real.sqrt]` — evaluating the final answer
- `ring` — for $z^{12} = (re^{i\pi/6})^{12} = r^{12} \cdot (e^{i\pi/6})^{12} = r^{12}$
- `field_simp` — clearing denominators in the residue
- `simp [Complex.exp_add, Complex.exp_mul_I]` — exponential arithmetic
- `calc` — for the chain equating contour integral to $2\pi i \cdot \mathrm{Res}$
- `positivity` — for $R > 0$, $\pi > 0$, $\sin > 0$
- `nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)]` — $\sqrt{3}$ arithmetic
- `gcongr` — for bounding the arc integral