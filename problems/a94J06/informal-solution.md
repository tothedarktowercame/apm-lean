

# APM a94J06: ∮ ζ̄/(ζ-z) dζ on the unit circle

## 1. Informal proof

**Why it's hard.** The integrand involves ζ̄, which is not holomorphic in ζ, so the Cauchy integral formula doesn't apply directly. You cannot simply say "the integral equals 2πi · (residue)" because ζ̄ is antiholomorphic, breaking the standard machinery.

**The key insight.** On the unit circle |ζ| = 1, we have ζ̄ = 1/ζ. This converts the antiholomorphic ζ̄ into a rational (hence meromorphic) function of ζ, and the integral becomes ∮ 1/(ζ(ζ-z)) dζ, which is computable by the residue theorem.

**Proof.**

On γ (the unit circle), |ζ| = 1, so ζ̄ = 1/ζ. Therefore:

$$\int_\gamma \frac{\bar{\zeta}}{\zeta - z}\,d\zeta = \int_\gamma \frac{1}{\zeta(\zeta - z)}\,d\zeta.$$

Use partial fractions: 1/(ζ(ζ-z)) = (1/z)(1/(ζ-z) - 1/ζ) for z ≠ 0.

**Case 1: |z| < 1 (z inside the unit disk), z ≠ 0.**

$$\int_\gamma \frac{1}{\zeta(\zeta-z)}\,d\zeta = \frac{1}{z}\left[\int_\gamma \frac{d\zeta}{\zeta-z} - \int_\gamma \frac{d\zeta}{\zeta}\right].$$

Both ζ = z and ζ = 0 are inside γ. By the Cauchy integral formula (∮ dζ/(ζ-a) = 2πi for a inside):

= (1/z)[2πi - 2πi] = 0.

**Case 1': z = 0.** The integral becomes ∮ 1/ζ² dζ. The residue of 1/ζ² at ζ = 0 is 0 (coefficient of ζ⁻¹ in the Laurent series 1/ζ²). So ∮ 1/ζ² dζ = 0.

**Case 2: |z| > 1 (z outside the unit disk).**

Now only ζ = 0 is inside γ (ζ = z is outside). So:

= (1/z)[0 - 2πi] = -2πi/z.

**Case 3: z ∈ γ (z on the unit circle).** The integral is improper — the integrand has a singularity at ζ = z on the contour. The integral does not converge as a standard integral (the singularity 1/(ζ-z) is not integrable on the curve). However, the Cauchy principal value exists: PV ∮ = -πi/z (half the "jump" between inside and outside values, by the Sokhotski-Plemelj formula). The jump is from 0 (inside) to -2πi/z (outside), so the PV is the average: (0 + (-2πi/z))/2 = -πi/z.

**Summary:**

$$\int_\gamma \frac{\bar{\zeta}}{\zeta-z}\,d\zeta = \begin{cases} 0 & \text{if } |z| < 1 \\ -2\pi i/z & \text{if } |z| > 1 \\ \text{PV} = -\pi i/z & \text{if } |z| = 1. \end{cases}$$

∎

**What connects.** This problem illustrates the interaction between holomorphic and antiholomorphic functions on curves. The trick ζ̄ = 1/ζ on the unit circle is fundamental — it converts problems involving conjugation into problems about rational functions, and is the basis of the Schwarz reflection principle and the theory of Hardy spaces on the disk. The jump from 0 to -2πi/z as z crosses the unit circle is the Sokhotski-Plemelj discontinuity, fundamental in the theory of singular integral equations and Riemann-Hilbert problems. The result also connects to the Cauchy transform: the integral is the Cauchy transform of the function ζ̄ restricted to the circle.

## 2. Lean 4 theorem statement

```lean
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex

noncomputable section

/-- The integral ∮ ζ̄/(ζ-z) dζ for |z| < 1 equals 0. -/
theorem conj_cauchy_inside
    {z : ℂ} (hz : ‖z‖ < 1) :
    ∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z) = 0 := by
  sorry

/-- The integral ∮ ζ̄/(ζ-z) dζ for |z| > 1 equals -2πi/z. -/
theorem conj_cauchy_outside
    {z : ℂ} (hz : 1 < ‖z‖) :
    ∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z) =
      -(2 * π * I) / z := by
  sorry

/-- On |ζ| = 1, ζ̄ = 1/ζ, converting the integrand to a
    rational function. -/
lemma conj_eq_inv_on_circle {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    starRingEnd ℂ ζ = ζ⁻¹ := by
  sorry

/-- Rewriting: ∮ ζ̄/(ζ-z) dζ = ∮ 1/(ζ(ζ-z)) dζ. -/
lemma conj_cauchy_eq_rational
    {z : ℂ} (hz : z ≠ 0) :
    ∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - z) =
      ∮ ζ in C(0, 1), 1 / (ζ * (ζ - z)) := by
  sorry

/-- Partial fractions: 1/(ζ(ζ-z)) = (1/z)(1/(ζ-z) - 1/ζ). -/
lemma partial_fractions {ζ z : ℂ} (hζ : ζ ≠ 0) (hz : z ≠ 0)
    (hζz : ζ ≠ z) :
    1 / (ζ * (ζ - z)) = (1 / z) * (1 / (ζ - z) - 1 / ζ) := by
  sorry

/-- The case z = 0: ∮ 1/ζ² dζ = 0. -/
lemma conj_cauchy_at_zero :
    ∮ ζ in C(0, 1), starRingEnd ℂ ζ / (ζ - 0) = 0 := by
  sorry

/-- For z on the circle: the integral diverges as a standard integral
    but the Cauchy principal value equals -πi/z. -/
theorem conj_cauchy_principal_value
    {z : ℂ} (hz : ‖z‖ = 1) :
    -- The PV is the average of inside (0) and outside (-2πi/z) limits
    (0 + (-(2 * π * I) / z)) / 2 = -(π * I) / z := by
  sorry

end
```

## 3. Mathlib cross-references

**Types/structures:**
- `circleIntegral` / `∮ ζ in C(0, 1)` — contour integral over the unit circle
- `starRingEnd ℂ` — complex conjugation as a ring endomorphism (ζ ↦ ζ̄)
- `Complex.I`, `Complex.normSq` — imaginary unit and |z|²
- `Metric.sphere (0 : ℂ) 1` — the unit circle as a set

**Key lemmas:**
- `Complex.circleIntegral_sub_inv_of_mem_ball` — ∮ 1/(ζ-a) dζ = 2πi for a inside the circle. Core Cauchy formula in Mathlib
- `Complex.circleIntegral_sub_inv_of_not_mem_closedBall` — ∮ 1/(ζ-a) dζ = 0 for a outside the circle
- `Complex.inv_eq_conj_div_normSq` — z⁻¹ = z̄/|z|² (for |z|=1 gives z⁻¹ = z̄)
- `Complex.normSq_eq_one_iff_norm_eq_one` — |z|² = 1 ↔ ‖z‖ = 1
- `circleIntegral_eq_zero_of_differentiableOn` — Cauchy's theorem (for the ∮ 1/(ζ-z) = 0 term when z is outside)
- `div_add_div_same` — algebraic manipulation for partial fractions
- `Complex.ofReal_mul_re` — for extracting 2πi computations

**Tactic hints:**
- `rw [conj_eq_inv_on_circle]` — converting ζ̄ to 1/ζ on the circle
- `rw [conj_cauchy_eq_rational hz]` — rewriting to rational form
- `simp [partial_fractions]` — applying partial fractions
- `rw [circleIntegral_sub_inv_of_mem_ball, circleIntegral_sub_inv_of_mem_ball]` — applying Cauchy formula twice
- `ring` — for the partial fractions identity and final simplification
- `field_simp` — clearing denominators
- `norm_num` — for ‖0‖ < 1
- `exact?` — finding the right circle integral lemma