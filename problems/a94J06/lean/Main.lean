import Mathlib

/-!
# APM a94J06 — a conjugate contour integral on the unit circle

## Statement repairs

None.

The theorem states all three cases. For a point on the circle, the ordinary
contour integral is not defined because the parametrized integrand is not
integrable; no principal-value convention is silently introduced.
-/

open Complex Real

noncomputable section

def apm_a94J06_integrand (z ζ : ℂ) : ℂ :=
  starRingEnd ℂ ζ / (ζ - z)

/-- On the unit circle, conjugation agrees with inversion. Reused from the
sorry-free inside/outside development at commit `6bbe1d7`. -/
lemma apm_a94J06_conj_eq_inv_on_circle {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    starRingEnd ℂ ζ = ζ⁻¹ :=
  (RCLike.inv_eq_conj hζ).symm

/-- Rational form of the conjugate integrand on the contour. -/
lemma apm_a94J06_integrand_eq_rational
    {ζ z : ℂ} (hζ : ‖ζ‖ = 1) (hne : ζ ≠ z) :
    apm_a94J06_integrand z ζ = (ζ * (ζ - z))⁻¹ := by
  have hζ0 : ζ ≠ 0 := by
    intro h
    rw [h] at hζ
    simp at hζ
  rw [apm_a94J06_integrand, div_eq_inv_mul,
    apm_a94J06_conj_eq_inv_on_circle hζ, mul_inv_rev]

/-- The contour integral can be rationalized pointwise, including at the pole
where both expressions use Mathlib's totalized inverse. -/
lemma apm_a94J06_integral_eq_rational {z : ℂ} :
    (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) =
      ∮ ζ in C(0, 1), ((ζ * (ζ - z))⁻¹ : ℂ) := by
  apply circleIntegral.integral_congr zero_le_one
  intro ζ hζ
  have hζn : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  by_cases hne : ζ = z
  · subst hne
    simp [apm_a94J06_integrand, div_eq_inv_mul]
  · exact apm_a94J06_integrand_eq_rational hζn hne

theorem apm_a94j06 (z : ℂ) :
    (‖z‖ < 1 →
      (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) = 0) ∧
    (1 < ‖z‖ →
      (∮ ζ in C(0, 1), apm_a94J06_integrand z ζ) =
        -(2 * Real.pi * Complex.I) / z) ∧
    (‖z‖ = 1 →
      ¬CircleIntegrable (apm_a94J06_integrand z) 0 1) := by
  /-
  CLOSER HOP 1: commit `6bbe1d7` is a sorry-free proof of the inside and
  outside evaluations, but predates the frozen theorem's third conjunct and
  does not prove boundary nonintegrability. Its core contour rationalization
  has been extracted above as the compiled lemmas
  `apm_a94J06_conj_eq_inv_on_circle`,
  `apm_a94J06_integrand_eq_rational`, and
  `apm_a94J06_integral_eq_rational`.

  Porting the remainder of that development closes the first two conjuncts by
  partial fractions and standard Cauchy-kernel integrals. The genuinely new
  bridge is the boundary case: after circle parametrization at the unique pole,
  prove the norm behaves like `1 / |t-t₀|` and is not interval-integrable.
  Searches found `circleIntegrable_sub_inv_iff`, which handles the bare Cauchy
  kernel, but no theorem transporting nonintegrability through the nonvanishing
  conjugate numerator. No statement defect was found.
  -/
  sorry
