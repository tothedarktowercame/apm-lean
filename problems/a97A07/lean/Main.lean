import Mathlib

open Complex Polynomial MeasureTheory Real Set

noncomputable section

variable (R : ℝ) (hR : 0 < R)

/-- The polynomial p(z) = ∏(z - z_k). -/
def apm_a97A07_p (zs : Fin n → ℂ) : Polynomial ℂ :=
  ∏ k, (Polynomial.X - Polynomial.C (zs k))

/-- The divided-difference kernel Q(ζ, z) = (p(ζ) - p(z))/(ζ - z),
    which is polynomial in z of degree n - 1. -/
def apm_a97A07_Q (zs : Fin n → ℂ) (ζ z : ℂ) : ℂ :=
  if z = ζ then (Polynomial.derivative (apm_a97A07_p zs)).aeval ζ
  else ((apm_a97A07_p zs).aeval ζ - (apm_a97A07_p zs).aeval z) / (ζ - z)

/-- The Hermite contour-integral interpolant. -/
def apm_a97A07_P (n : ℕ) (zs : Fin n → ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  (1 / (2 * π * I)) • ∫ t in (0 : ℝ)..1,
    ((f (γ t) / (apm_a97A07_p zs).aeval (γ t)) * apm_a97A07_Q zs (γ t) z) * deriv γ t

/-- Helper: Q(ζ, z) is a polynomial in z of degree at most n - 1. -/
theorem apm_a97A07_Q_polynomial_in_z
    (n : ℕ) (hn : 0 < n) (zs : Fin n → ℂ) (ζ : ℂ) :
    ∃ q : Polynomial ℂ, q.natDegree ≤ n - 1 ∧
      ∀ z : ℂ, z ≠ ζ → q.aeval z = apm_a97A07_Q zs ζ z := by sorry

/-- P is a polynomial of degree at most n - 1. -/
theorem apm_a97A07_P_polynomial
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ) -- simplified: entire
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) :
    ∃ P_poly : Polynomial ℂ,
      P_poly.natDegree ≤ n - 1 ∧
      ∀ z : ℂ, apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) z =
        P_poly.aeval z := by sorry

/-- Interpolation property: P(z_k) = f(z_k) for each k.
    Uses Cauchy's integral formula. -/
theorem apm_a97A07_interpolates
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ)
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R)
    (k : Fin n) :
    apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) (zs k) = f (zs k) := by sorry

/-- Main theorem: P is a polynomial of degree ≤ n - 1 and interpolates f
    at z_1, ..., z_n. (Using a circle of radius R as the Jordan curve
    enclosing all the z_k.) -/
theorem apm_a97A07_main
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ)
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) :
    ∃ P_poly : Polynomial ℂ,
      P_poly.natDegree ≤ n - 1 ∧
      (∀ z : ℂ, apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) z =
        P_poly.aeval z) ∧
      (∀ k : Fin n, P_poly.aeval (zs k) = f (zs k)) := by
  rcases apm_a97A07_P_polynomial n hn zs zs_distinct f hf R hR hzs_in with
    ⟨P_poly, hdeg, hP⟩
  refine ⟨P_poly, hdeg, hP, ?_⟩
  intro k
  rw [← hP (zs k)]
  exact apm_a97A07_interpolates n hn zs zs_distinct f hf R hR hzs_in k
