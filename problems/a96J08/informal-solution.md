

## 1. Informal proof

**Why it's hard:** The integrand e^{ωx}/(1 - e^x) has poles at every x = 2πin (n ∈ ℤ), so the real line passes through a pole at x = 0, requiring the integral to be interpreted as a principal value. Choosing the right contour that captures exactly one pole while producing a functional equation is the crux.

**The key insight:** Use a rectangular contour with vertices at -R, R, R + 2πi, -R + 2πi. The integrand has a period shift: replacing x by x + 2πi multiplies e^{ωx} by e^{2πiω}, so the integral along the top edge is -e^{2πiω} times the integral along the bottom. The only pole inside the rectangle is at x = 0 (or, with an indentation, we capture the residue there).

**Proof:**

The integral is understood as the principal value, or equivalently, we indent around x = 0. Consider the rectangular contour Γ with vertices at -R - εi, R - εi, R + 2πi - εi, -R + 2πi - εi (shifted down by ε to avoid the pole at 0, which then sits inside the rectangle; alternatively, indent with a small semicircle). Actually, the cleaner approach: use the rectangle with corners -R, R, R + 2πi, -R + 2πi and indent around x = 0 and x = 2πi with small semicircles of radius δ.

Let me use the standard approach. Define I = ∫_{-∞}^{∞} e^{ωx}/(1 - e^x) dx (principal value at x = 0). Take the rectangular contour with corners at -R, R, R + 2πi, -R + 2πi, traversed counterclockwise, with small semicircular indentations of radius δ around the poles at 0 and 2πi.

**Bottom edge** (from -R to R, indented around 0): This approaches I as R → ∞, δ → 0 (with the half-residue contribution from the indent).

**Top edge** (from R + 2πi to -R + 2πi, indented around 2πi): Substituting z = x + 2πi, we have e^{ωz} = e^{ω(x+2πi)} = e^{2πiω}e^{ωx} and 1 - e^z = 1 - e^{x+2πi} = 1 - e^x. The top edge traverses right-to-left, giving -e^{2πiω}I (with the corresponding half-residue from the indent at 2πi).

**Right edge** (from R to R + 2πi): |e^{ωz}/(1-e^z)| with z = R + iy, 0 ≤ y ≤ 2π. We have |e^{ωz}| = e^{Re(ω)R} and |1 - e^z| ≥ e^R - 1 ~ e^R. So the integrand is O(e^{(Re(ω)-1)R}) → 0 since Re(ω) < 1. The integral over this edge → 0.

**Left edge** (from -R + 2πi to -R): |e^{ωz}| = e^{Re(ω)(-R)} → 0 since Re(ω) > 0. Meanwhile |1/(1-e^z)| → 1/(1-0) = 1 as Re(z) → -∞. So this edge contributes 0.

**Indentation at 0**: The residue of e^{ωz}/(1-e^z) at z = 0 is e^{ω·0}/(-e^0) = -1. The semicircular indent (going above the pole, clockwise) contributes -πi · (-1) = πi (half the residue, with sign depending on orientation). Similarly, the indent at 2πi: the residue is e^{2πiω}/(-e^{2πi}) = -e^{2πiω}, and the clockwise semicircle contributes πi · e^{2πiω}.

Actually, let's be more careful. The pole at z = 0 of f(z) = e^{ωz}/(1 - e^z): since 1 - e^z = -z - z²/2 - ... near z = 0, the residue is lim_{z→0} z · e^{ωz}/(1-e^z) = 1·1/(-1) = -1.

Since there are no poles strictly inside the contour (we've indented around both), the full contour integral is 0. Collecting terms:

$$0 = I + 0 + (-e^{2\pi i\omega}I) + 0 + \pi i \cdot(-1)\cdot(-1) + \pi i \cdot(-e^{2\pi i\omega})\cdot(-1)$$

Wait — let me be precise about the indentation contributions. With the bottom edge going left-to-right and indenting above the pole at 0 (small semicircle of radius δ in the upper half), this semicircle is traversed clockwise, contributing -πi · Res_{z=0} = -πi(-1) = πi. At z = 2πi on the top edge (going right-to-left), we indent below the pole (into the rectangle), also clockwise, contributing -πi · Res_{z=2πi} = -πi(-e^{2πiω}) = πie^{2πiω}.

So: I - e^{2πiω}I + πi + πie^{2πiω} = 0.

Therefore: I(1 - e^{2πiω}) = -πi(1 + e^{2πiω}).

$$I = \frac{-\pi i(1 + e^{2\pi i\omega})}{1 - e^{2\pi i\omega}}$$

Factor out e^{πiω}:

$$I = \frac{-\pi i \cdot e^{\pi i\omega}(e^{-\pi i\omega} + e^{\pi i\omega})}{-e^{\pi i\omega}(e^{-\pi i\omega} - e^{\pi i\omega})} = \frac{\pi i \cdot 2\cos(\pi\omega)}{-2i\sin(\pi\omega)} = \frac{-\pi\cos(\pi\omega)}{\sin(\pi\omega)}$$

$$\boxed{I = -\pi\cot(\pi\omega)} = \frac{\pi}{\tan(\pi\omega)}$$

Or equivalently: I = π cot(π(1-ω)) = -π cot(πω). ∎

**What connects:** This is a classic contour integration over a rectangular period-cell, exploiting the periodicity of e^z to create a functional equation I·(1 - e^{2πiω}) = known. The constraint 0 < Re(ω) < 1 ensures convergence at ±∞ (the left/right edges vanish). The same technique evaluates ∫ x^{s-1}/(e^x - 1)dx (the Γ(s)ζ(s) integral) via the Hankel contour — this problem is a close relative. The answer π cot(πω) is also connected to the reflection formula Γ(ω)Γ(1-ω) = π/sin(πω) and partial fraction expansion of cot.

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
- `Complex.exp_add` — e^{a+b} = e^a · e^b (for the period shift)
- `Complex.exp_int_mul_two_pi_mul_I` — e^{2πin} = 1 (periodicity of e^z)
- `Complex.abs_exp` — |e^z| = e^{Re(z)} (for edge estimates)
- `Complex.cos_pi_div_two` / trig identities
- `Complex.sin_ne_zero_iff` — sin(πω) ≠ 0 when ω ∉ ℤ
- `intervalIntegral.norm_integral_le_of_norm_le` — ML estimate for interval integrals
- `MeasureTheory.integral_add_adjacent_intervals` — splitting integrals
- `Complex.ofReal_cos`, `Complex.ofReal_sin` — coercion lemmas
- `hasSum_zeta_of_gt_one` / `riemannZeta` — related but not directly used
- `Real.tendsto_exp_atTop` — e^R → ∞ (for right edge vanishing)
- `tendsto_exp_neg_atTop_nhds_zero` — e^{-R} → 0 (for left edge vanishing)
- `Complex.cos_div_sin_eq_cot` — if it exists; otherwise manual cot definition
- `norm_div_le` — for bounding |f/g|

**Tactic hints:**
- `field_simp` — clear denominators in the cot(πω) expression and partial fractions
- `ring` — verify e^{πiω} factorization algebra
- `nlinarith` — close Re(ω) - 1 < 0 and similar real arithmetic
- `positivity` — for 0 < δ, 0 < R, sin(πω) ≠ 0 goals
- `simp [Complex.exp_add, Complex.exp_mul_I]` — simplify exponentials
- `norm_num` — for concrete π arithmetic
- `gcongr` — monotone estimates on the edge integrals
- `refine Tendsto.congr ?_ ?_` — match limit expressions up to rearrangement
- `conv` — rewrite integrand into partial fraction form inside the integral