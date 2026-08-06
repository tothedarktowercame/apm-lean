import Mathlib

/-!
# APM m99A01

## Statement repairs

The source does not specify the admissible function class. The functional is
encoded on `C¹` curves, and extremals are `C²` stationary curves, the standard
minimal regularity needed for the classical Euler--Lagrange formulation.

## Encoding questions

An extremal is encoded intrinsically by vanishing first variation for every
`C¹` endpoint-fixing variation, rather than by taking the Euler--Lagrange ODE
as its definition.
-/

open Set intervalIntegral

/-- The functional in the problem. -/
noncomputable def apm_m99A01_functional (y : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(Real.pi / 2), (deriv y t) ^ 2 + (y t) ^ 2 + 2 * y t

/-- Curves satisfying the stated endpoint constraints. -/
def apm_m99A01_admissible : Set (ℝ → ℝ) :=
  {y | ContDiff ℝ 1 y ∧ y 0 = 0 ∧ y (Real.pi / 2) = 0}

/-- Stationarity under all endpoint-fixing first variations. -/
def apm_m99A01_stationary (y : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η 0 = 0 → η (Real.pi / 2) = 0 →
    HasDerivAt
      (fun s ↦ apm_m99A01_functional (fun t ↦ y t + s * η t)) 0 0

/-- The unique candidate extremal obtained from the boundary-value problem. -/
noncomputable def apm_m99A01_extremal (t : ℝ) : ℝ :=
  Real.cosh t - Real.tanh (Real.pi / 4) * Real.sinh t - 1

theorem apm_m99a01 :
    (∀ y : ℝ → ℝ,
      (ContDiff ℝ 2 y ∧ y ∈ apm_m99A01_admissible ∧ apm_m99A01_stationary y) ↔
        y = apm_m99A01_extremal) ∧
    apm_m99A01_extremal ∈ apm_m99A01_admissible ∧
    (∀ y ∈ apm_m99A01_admissible,
      apm_m99A01_functional apm_m99A01_extremal ≤ apm_m99A01_functional y) ∧
    ¬ ∃ y ∈ apm_m99A01_admissible, ∀ z ∈ apm_m99A01_admissible,
      apm_m99A01_functional z ≤ apm_m99A01_functional y := by
  sorry
