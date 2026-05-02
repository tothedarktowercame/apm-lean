# Proof outline — a97A07

Source: claude-1 batch 20260502 (sequence apm-daily-batch.md).

## Theorem statements (Lean)

```lean
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.MeasureTheory.Integral.CircleIntegral

open Complex Polynomial MeasureTheory Set

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
  (1 / (2 * π * I)) • ∮ ζ in γ,
    (f ζ / (apm_a97A07_p zs).aeval ζ) * apm_a97A07_Q zs ζ z

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
      (∀ k : Fin n, P_poly.aeval (zs k) = f (zs k)) := by sorry
```


## Mathlib cross-references

**Types/structures:**
- `ℂ` / `Complex` — complex numbers
- `Polynomial ℂ` — polynomial ring over ℂ
- `Polynomial.aeval` — polynomial evaluation as algebra hom
- `Polynomial.natDegree`, `Polynomial.degree` — polynomial degree
- `Polynomial.derivative` — formal derivative
- `circleIntegral` (`∮ ζ in C(c, R)`) — circle contour integral
- `AnalyticOn`, `AnalyticAt` — analyticity
- `Function.Injective` — distinctness of nodes
- `Fin n` — indexing the nodes

**Key lemmas:**
- `Complex.circleIntegral_sub_inv_smul_of_differentiable` — Cauchy integral formula: ∮ f(ζ)/(ζ-z) dζ = 2πi f(z)
- `circleIntegral.integral_sub` / `circleIntegral.integral_add` — linearity of contour integrals
- `circleIntegral.integral_const_smul` — pulling constants out of contour integrals
- `Polynomial.sub_dvd_eval_sub` — (ζ - z) ∣ (p(ζ) - p(z)) divisibility
- `Polynomial.X_sub_C_dvd_sub_C_of_isRoot` — analogous root-factor lemma
- `geom_series_def` / `Finset.geom_sum_eq` — ζ^j - z^j = (ζ - z)(ζ^{j-1} + ζ^{j-2}z + ...)
- `Polynomial.aeval_geom_series` / `Commute.geom_sum₂_mul`
- `circleIntegral.integral_eq_zero_of_isClosed` / `Complex.integral_circleMap` — Cauchy's theorem
- `MeasureTheory.integral_finset_sum` / `circleIntegral.integral_finset_sum` — interchange sum and integral
- `Polynomial.eval_root` — p(z_k) = 0 since z_k is a root
- `Polynomial.IsRoot` / `Polynomial.dvd_iff_isRoot` — root characterization
- `Polynomial.degree_prod_le` / `Polynomial.natDegree_prod` — degree of product
- `AnalyticOn.div` — analytic on region where denominator nonzero
- `Polynomial.coeff_natDegree_le_of_natDegree_le` — coefficient bounds
- `Complex.norm_eq_abs` — bridge to absolute value
- `IsCompact.exists_isMaxOn` — for ML estimates if needed

**Tactic hints:**
- `field_simp` — clear (ζ - z) and p(ζ) denominators
- `ring` — polynomial identity p(ζ) - p(z) = (ζ - z) Q(ζ, z)
- `simp [apm_a97A07_p, apm_a97A07_Q]` — unfold definitions
- `induction n` — induction on number of nodes
- `nlinarith` — close 0 < R, n ≥ 1 arithmetic
- `positivity` — for 0 < R, 0 < 2π
- `apply Polynomial.degree_le_of_natDegree_le` — degree bound assembly
- `refine ⟨?_, ?_, ?_⟩` — assemble three-part conclusion
- `intro z hz` / `intro k` — work pointwise / per-node
- `exact?` — search for Cauchy integral formula in the right form
- `convert` — match expressions modulo small rewrites
- `have hp_root : (apm_a97A07_p zs).aeval (zs k) = 0 := by ...` — key root fact
- `simp [Polynomial.aeval_prod, Polynomial.aeval_X_sub_C]` — evaluate the product polynomial

## Blockers

- All theorem bodies are `sorry`. Codex cleanup pass to attempt closure.
- Mathlib lemma names above are conjectural — verify via `exact?` / `apply?`.
