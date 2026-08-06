import Mathlib

/-!
# APM m98J04

## Statement repairs

The source does not state regularity assumptions. The Euler--Lagrange part is
minimally stated for a `C²` Lagrangian and a `C²` stationary curve, while the
arc-length minimization ranges over `C¹` graph curves. The two endpoints are
assumed to have distinct horizontal coordinates, ordered as `a < b`, as is
required by the graph parametrization used in the question.

## Encoding questions

Stationarity means vanishing first variation against every `C¹` variation
which fixes both endpoints. Partial derivatives of the Lagrangian are encoded
as ordinary derivatives with the other two arguments held fixed.
-/

open Set intervalIntegral

/-- The variational functional associated to a first-order Lagrangian. -/
noncomputable def apm_m98J04_functional
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, F x (y x) (deriv y x)

/-- Vanishing first variation under endpoint-fixing variations. -/
def apm_m98J04_stationary
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ η : ℝ → ℝ, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
    HasDerivAt
      (fun t ↦ apm_m98J04_functional F a b (fun x ↦ y x + t * η x)) 0 0

/-- The pointwise Euler--Lagrange equation along a curve. -/
def apm_m98J04_eulerLagrange
    (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ) : Prop :=
  ∀ x ∈ Ioo a b,
    HasDerivAt
      (fun t ↦ deriv (fun p ↦ F t (y t) p) (deriv y t))
      (deriv (fun q ↦ F x q (deriv y x)) (y x)) x

/-- Length of a plane curve presented as a graph. -/
noncomputable def apm_m98J04_arcLength (a b : ℝ) (y : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, Real.sqrt (1 + (deriv y x) ^ 2)

/-- The line graph joining `(a, α)` and `(b, β)`. -/
noncomputable def apm_m98J04_line (a b α β : ℝ) (x : ℝ) : ℝ :=
  α + ((β - α) / (b - a)) * (x - a)

/-- `C¹` graph curves with the prescribed endpoints. -/
def apm_m98J04_admissible (a b α β : ℝ) : Set (ℝ → ℝ) :=
  {y | ContDiff ℝ 1 y ∧ y a = α ∧ y b = β}

theorem apm_m98j04 :
    (∀ (F : ℝ → ℝ → ℝ → ℝ) (a b : ℝ) (y : ℝ → ℝ),
      a < b →
      ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ ↦ F p.1 p.2.1 p.2.2) →
      ContDiff ℝ 2 y →
      apm_m98J04_stationary F a b y →
      apm_m98J04_eulerLagrange F a b y) ∧
    ∀ (a b α β : ℝ), a < b →
      apm_m98J04_line a b α β ∈ apm_m98J04_admissible a b α β ∧
      ∀ y ∈ apm_m98J04_admissible a b α β,
        apm_m98J04_arcLength a b (apm_m98J04_line a b α β) ≤
          apm_m98J04_arcLength a b y := by
  constructor
  · /-
    Boundary: deriving the pointwise Euler--Lagrange equation from the frozen
    stationarity predicate requires differentiating an interval integral with
    respect to the variation parameter, integration by parts, and a fundamental
    lemma for endpoint-zero `C¹` test variations. I searched Mathlib's
    `HasDerivAt`-under-integral, interval integration-by-parts, bump-function,
    and fundamental-lemma APIs; I did not find an assembled route matching this
    bespoke three-variable Lagrangian encoding.
    -/
    sorry
  · intro a b α β hab
    constructor
    · refine ⟨?_, ?_, ?_⟩
      · unfold apm_m98J04_line
        fun_prop
      · simp [apm_m98J04_line]
      · have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
        simp [apm_m98J04_line, hba]
    · /-
      Boundary: global minimality is the convexity/Jensen estimate for
      `p ↦ sqrt (1 + p²)`, followed by the fundamental theorem of calculus for
      an arbitrary globally `C¹` competitor to identify the integral of its
      derivative with `β - α`. I searched `Convex`, `intervalIntegral`, and
      arc-length APIs; the required Jensen estimate and endpoint derivative
      identity were not available in a directly composable form in this pass.
      The line's `C¹` regularity and both endpoint constraints are proved above.
      -/
      sorry
