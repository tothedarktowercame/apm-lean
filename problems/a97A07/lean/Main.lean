import Mathlib

open Complex Polynomial MeasureTheory Real Set

noncomputable section

variable (R : ℝ) (hR : 0 < R)

/-- The polynomial p(z) = ∏(z - z_k). -/
def apm_a97A07_p (zs : Fin n → ℂ) : Polynomial ℂ :=
  ∏ k, (Polynomial.X - Polynomial.C (zs k))

@[simp] lemma apm_a97A07_p_eval_zs (zs : Fin n → ℂ) (k : Fin n) :
    (apm_a97A07_p zs).eval (zs k) = 0 := by
  simp only [apm_a97A07_p, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _)

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
      ∀ z : ℂ, z ≠ ζ → q.aeval z = apm_a97A07_Q zs ζ z := by
  let p := apm_a97A07_p zs
  let q := (p - Polynomial.C (p.eval ζ)) /ₘ
    (Polynomial.X - Polynomial.C ζ)
  refine ⟨q, ?_, ?_⟩
  · rw [show q.natDegree =
        (p - Polynomial.C (p.eval ζ)).natDegree - 1 by
      simpa [q] using
        Polynomial.natDegree_divByMonic
          (p - Polynomial.C (p.eval ζ))
          (Polynomial.monic_X_sub_C ζ)]
    apply Nat.sub_le_sub_right
    calc
      (p - Polynomial.C (p.eval ζ)).natDegree
          ≤ max p.natDegree (Polynomial.C (p.eval ζ)).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ n := by
        simp [p, apm_a97A07_p]
  · intro z hz
    have hroot :
        Polynomial.IsRoot (p - Polynomial.C (p.eval ζ)) ζ := by
      simp [Polynomial.IsRoot]
    have hmul :
        (Polynomial.X - Polynomial.C ζ) * q =
          p - Polynomial.C (p.eval ζ) := by
      simpa [q] using
        (Polynomial.mul_divByMonic_eq_iff_isRoot
          (p := p - Polynomial.C (p.eval ζ)) (a := ζ)).2 hroot
    have heval := congrArg (fun r : Polynomial ℂ => r.eval z) hmul
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at heval
    change q.eval z = apm_a97A07_Q zs ζ z
    rw [apm_a97A07_Q, if_neg hz]
    change q.eval z = (p.eval ζ - p.eval z) / (ζ - z)
    apply (eq_div_iff (sub_ne_zero.mpr hz.symm)).2
    linear_combination -heval

/-- P is a polynomial of degree at most n - 1. -/
theorem apm_a97A07_P_polynomial
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ) -- simplified: entire
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R) :
    ∃ P_poly : Polynomial ℂ,
      P_poly.natDegree ≤ n - 1 ∧
      ∀ z : ℂ, apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) z =
        P_poly.aeval z := by
  /-
  Remaining construction: use the quotient polynomial from
  `apm_a97A07_Q_polynomial_in_z`, expand it in the monomial basis of degrees
  `< n`, and integrate its finitely many coefficient functions.  The contour
  stays away from every root by `hzs_in`, so those coefficient functions are
  continuous and interval-integrable.
  -/
  sorry

/-- Interpolation property: P(z_k) = f(z_k) for each k.
    Uses Cauchy's integral formula. -/
theorem apm_a97A07_interpolates
    (n : ℕ) (hn : 0 < n)
    (zs : Fin n → ℂ) (zs_distinct : Function.Injective zs)
    (f : ℂ → ℂ) (hf : AnalyticOn ℂ f univ)
    (R : ℝ) (hR : 0 < R) (hzs_in : ∀ k, ‖zs k‖ < R)
    (k : Fin n) :
    apm_a97A07_P n zs f (fun t => R * Complex.exp (2 * π * I * t)) (zs k) = f (zs k) := by
  /-
  Remaining construction: at `zs k`, cancel the factor
  `(ζ - zs k)` between `Q` and `p`, reparameterize `t ∈ [0,1]` as
  `θ = 2πt`, and apply
  `DifferentiableOn.circleIntegral_sub_inv_smul`.
  -/
  sorry

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
