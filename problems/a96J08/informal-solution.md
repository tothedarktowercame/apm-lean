## 1. Informal proof

**Why it's hard:** The integrand $e^{\omega x}/(1 - e^x)$ has poles at every $x = 2\pi in$ ($n \in \mathbb{Z}$), so the real line passes through a pole at $x = 0$, requiring the integral to be interpreted as a principal value. Choosing the right contour that captures exactly one pole while producing a functional equation is the crux.

**The key insight:** Use a rectangular contour with vertices at $-R$, $R$, $R + 2\pi i$, $-R + 2\pi i$. The integrand has a period shift: replacing $x$ by $x + 2\pi i$ multiplies $e^{\omega x}$ by $e^{2\pi i\omega}$, so the integral along the top edge is $-e^{2\pi i\omega}$ times the integral along the bottom. The only pole inside the rectangle is at $x = 0$ (or, with an indentation, we capture the residue there).

**Proof:**

The integral is understood as the principal value, or equivalently, we indent around $x = 0$. Consider the rectangular contour $\Gamma$ with vertices at $-R - \varepsilon i$, $R - \varepsilon i$, $R + 2\pi i - \varepsilon i$, $-R + 2\pi i - \varepsilon i$ (shifted down by $\varepsilon$ to avoid the pole at 0, which then sits inside the rectangle; alternatively, indent with a small semicircle). Actually, the cleaner approach: use the rectangle with corners $-R$, $R$, $R + 2\pi i$, $-R + 2\pi i$ and indent around $x = 0$ and $x = 2\pi i$ with small semicircles of radius $\delta$.

Let me use the standard approach. Define $I = \int_{-\infty}^{\infty} e^{\omega x}/(1 - e^x)\, dx$ (principal value at $x = 0$). Take the rectangular contour with corners at $-R$, $R$, $R + 2\pi i$, $-R + 2\pi i$, traversed counterclockwise, with small semicircular indentations of radius $\delta$ around the poles at 0 and $2\pi i$.

**Bottom edge** (from $-R$ to $R$, indented around 0): This approaches $I$ as $R \to \infty$, $\delta \to 0$ (with the half-residue contribution from the indent).

**Top edge** (from $R + 2\pi i$ to $-R + 2\pi i$, indented around $2\pi i$): Substituting $z = x + 2\pi i$, we have $e^{\omega z} = e^{\omega(x+2\pi i)} = e^{2\pi i\omega}e^{\omega x}$ and $1 - e^z = 1 - e^{x+2\pi i} = 1 - e^x$. The top edge traverses right-to-left, giving $-e^{2\pi i\omega}I$ (with the corresponding half-residue from the indent at $2\pi i$).

**Right edge** (from $R$ to $R + 2\pi i$): $|e^{\omega z}/(1-e^z)|$ with $z = R + iy$, $0 \leq y \leq 2\pi$. We have $|e^{\omega z}| = e^{\mathrm{Re}(\omega)R}$ and $|1 - e^z| \geq e^R - 1 \sim e^R$. So the integrand is $O(e^{(\mathrm{Re}(\omega)-1)R}) \to 0$ since $\mathrm{Re}(\omega) < 1$. The integral over this edge $\to 0$.

**Left edge** (from $-R + 2\pi i$ to $-R$): $|e^{\omega z}| = e^{\mathrm{Re}(\omega)(-R)} \to 0$ since $\mathrm{Re}(\omega) > 0$. Meanwhile $|1/(1-e^z)| \to 1/(1-0) = 1$ as $\mathrm{Re}(z) \to -\infty$. So this edge contributes 0.

**Indentation at 0**: The residue of $e^{\omega z}/(1-e^z)$ at $z = 0$ is $e^{\omega\cdot 0}/(-e^0) = -1$. The semicircular indent (going above the pole, clockwise) contributes $-\pi i \cdot (-1) = \pi i$ (half the residue, with sign depending on orientation). Similarly, the indent at $2\pi i$: the residue is $e^{2\pi i\omega}/(-e^{2\pi i}) = -e^{2\pi i\omega}$, and the clockwise semicircle contributes $\pi i \cdot e^{2\pi i\omega}$.

Actually, let's be more careful. The pole at $z = 0$ of $f(z) = e^{\omega z}/(1 - e^z)$: since $1 - e^z = -z - z^{2}/2 - \ldots$ near $z = 0$, the residue is $\lim_{z\to 0} z \cdot e^{\omega z}/(1-e^z) = 1\cdot 1/(-1) = -1$.

Since there are no poles strictly inside the contour (we've indented around both), the full contour integral is 0. Collecting terms:

$$0 = I + 0 + (-e^{2\pi i\omega}I) + 0 + \pi i \cdot(-1)\cdot(-1) + \pi i \cdot(-e^{2\pi i\omega})\cdot(-1)$$

Wait — let me be precise about the indentation contributions. With the bottom edge going left-to-right and indenting above the pole at 0 (small semicircle of radius $\delta$ in the upper half), this semicircle is traversed clockwise, contributing $-\pi i \cdot \mathrm{Res}_{z=0} = -\pi i(-1) = \pi i$. At $z = 2\pi i$ on the top edge (going right-to-left), we indent below the pole (into the rectangle), also clockwise, contributing $-\pi i \cdot \mathrm{Res}_{z=2\pi i} = -\pi i(-e^{2\pi i\omega}) = \pi ie^{2\pi i\omega}$.

So: $I - e^{2\pi i\omega}I + \pi i + \pi ie^{2\pi i\omega} = 0$.

Therefore: $I(1 - e^{2\pi i\omega}) = -\pi i(1 + e^{2\pi i\omega})$.

$$I = \frac{-\pi i(1 + e^{2\pi i\omega})}{1 - e^{2\pi i\omega}}$$

Factor out $e^{\pi i\omega}$:

$$I = \frac{-\pi i \cdot e^{\pi i\omega}(e^{-\pi i\omega} + e^{\pi i\omega})}{-e^{\pi i\omega}(e^{-\pi i\omega} - e^{\pi i\omega})} = \frac{\pi i \cdot 2\cos(\pi\omega)}{-2i\sin(\pi\omega)} = \frac{-\pi\cos(\pi\omega)}{\sin(\pi\omega)}$$

$$\boxed{I = -\pi\cot(\pi\omega)} = \frac{\pi}{\tan(\pi\omega)}$$

Or equivalently: $I = \pi \operatorname{cot}(\pi(1-\omega)) = -\pi \operatorname{cot}(\pi\omega)$. ∎

**What connects:** This is a classic contour integration over a rectangular period-cell, exploiting the periodicity of $e^z$ to create a functional equation $I\cdot(1 - e^{2\pi i\omega}) =$ known. The constraint $0 < \mathrm{Re}(\omega) < 1$ ensures convergence at $\pm\infty$ (the left/right edges vanish). The same technique evaluates $\int x^{s-1}/(e^x - 1)dx$ (the $\Gamma(s)\zeta(s)$ integral) via the Hankel contour — this problem is a close relative. The answer $\pi \operatorname{cot}(\pi\omega)$ is also connected to the reflection formula $\Gamma(\omega)\Gamma(1-\omega) = \pi/\sin(\pi\omega)$ and partial fraction expansion of cot.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegrableOn

open Complex MeasureTheory Real Set Filter

noncomputable section

/-- The integrand e^{ωx}/(1 - e^x) is integrable on ℝ as a principal value
    when 0 < Re(ω) < 1. -/
theorem apm_a96J08_integrable
    (ω : ℂ) (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) (δ : ℝ) (hδ : 0 < δ) :
    IntegrableOn (fun x : ℝ => Complex.exp (ω * x) / (1 - Complex.exp x))
      (Iio (-δ) ∪ Ioi δ) volume := by sorry

/-- The vertical edge integral vanishes as R → ∞ (right edge). -/
theorem apm_a96J08_right_edge_vanishes
    (ω : ℂ) (hre_lt : ω.re < 1) :
    Tendsto (fun R : ℝ => ∫ y in (0:ℝ)..2 * π,
      Complex.exp (ω * (R + y * I)) / (1 - Complex.exp (R + y * I)))
      atTop (nhds 0) := by sorry

/-- The vertical edge integral vanishes as R → ∞ (left edge). -/
theorem apm_a96J08_left_edge_vanishes
    (ω : ℂ) (hre_pos : 0 < ω.re) :
    Tendsto (fun R : ℝ => ∫ y in (0:ℝ)..2 * π,
      Complex.exp (ω * (-R + y * I)) / (1 - Complex.exp (-R + y * I)))
      atTop (nhds 0) := by sorry

/-- Residue of e^{ωz}/(1 - e^z) at z = 0 is -1. -/
theorem apm_a96J08_residue_zero
    (ω : ℂ) :
    Filter.Tendsto (fun z : ℂ => z * (Complex.exp (ω * z) / (1 - Complex.exp z)))
      (nhds 0) (nhds (-1)) := by sorry

/-- Main result: the integral equals -π cot(πω). -/
theorem apm_a96J08_main
    (ω : ℂ) (hre_pos : 0 < ω.re) (hre_lt : ω.re < 1) :
    Tendsto (fun δ : ℝ =>
      ∫ x in -δ⁻¹..(-δ), Complex.exp (ω * x) / (1 - Complex.exp x) +
      ∫ x in δ..δ⁻¹, Complex.exp (ω * x) / (1 - Complex.exp x))
      (nhdsWithin 0 (Ioi 0))
      (nhds (-π * Complex.cos (π * ω) / Complex.sin (π * ω))) := by sorry
```

## 3. Mathlib cross-references

**Types/structures:**
- `ℂ` / `Complex` — complex numbers
- `Complex.re`, `Complex.im` — real/imaginary parts
- `Complex.exp` — complex exponential
- `Complex.sin`, `Complex.cos` — complex trig functions
- `MeasureTheory.IntegrableOn` — integrability on a set
- `intervalIntegral` (`∫ x in a..b`) — oriented real integral
- `Filter.Tendsto`, `nhds`, `nhdsWithin`, `atTop` — limit infrastructure
- `Complex.I` — imaginary unit

**Key lemmas:**
- `Complex.exp_add` — $e^{a+b} = e^a \cdot e^b$ (for the period shift)
- `Complex.exp_int_mul_two_pi_mul_I` — $e^{2\pi in} = 1$ (periodicity of $e^z$)
- `Complex.abs_exp` — $|e^z| = e^{\mathrm{Re}(z)}$ (for edge estimates)
- `Complex.cos_pi_div_two` / trig identities
- `Complex.sin_ne_zero_iff` — $\sin(\pi\omega) \neq 0$ when $\omega \notin \mathbb{Z}$
- `intervalIntegral.norm_integral_le_of_norm_le` — ML estimate for interval integrals
- `MeasureTheory.integral_add_adjacent_intervals` — splitting integrals
- `Complex.ofReal_cos`, `Complex.ofReal_sin` — coercion lemmas
- `hasSum_zeta_of_gt_one` / `riemannZeta` — related but not directly used
- `Real.tendsto_exp_atTop` — $e^R \to \infty$ (for right edge vanishing)
- `tendsto_exp_neg_atTop_nhds_zero` — $e^{-R} \to 0$ (for left edge vanishing)
- `Complex.cos_div_sin_eq_cot` — if it exists; otherwise manual cot definition
- `norm_div_le` — for bounding $|f/g|$

**Tactic hints:**
- `field_simp` — clear denominators in the $\operatorname{cot}(\pi\omega)$ expression and partial fractions
- `ring` — verify $e^{\pi i\omega}$ factorization algebra
- `nlinarith` — close $\mathrm{Re}(\omega) - 1 < 0$ and similar real arithmetic
- `positivity` — for $0 < \delta$, $0 < R$, $\sin(\pi\omega) \neq 0$ goals
- `simp [Complex.exp_add, Complex.exp_mul_I]` — simplify exponentials
- `norm_num` — for concrete $\pi$ arithmetic
- `gcongr` — monotone estimates on the edge integrals
- `refine Tendsto.congr ?_ ?_` — match limit expressions up to rearrangement
- `conv` — rewrite integrand into partial fraction form inside the integral
