import Mathlib

/-!
# APM m02J01

## Statement repairs

The spelling `primative` in the source is read as `primitive`; no mathematical
change is made.

## Encoding notes

The statement uses Mathlib's genuine LF-topological test-function and
distribution spaces.  Distributional differentiation is exposed by its
defining action on the pointwise derivative of every bundled test function.
-/

open MeasureTheory Set TopologicalSpace
open scoped Distributions ContDiff

def apm_m02j01_IsDistributionalDerivative
    (v u : Distribution (⊤ : Opens ℝ) ℝ ⊤) : Prop :=
  ∀ φ dφ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
    (∀ x : ℝ, dφ x = deriv (φ : ℝ → ℝ) x) → u φ = -v dφ

theorem apm_m02j01 :
    (∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
      (∫ x : ℝ, φ x) = 0 ↔
        ∃ ψ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
          ∀ x : ℝ, φ x = deriv (ψ : ℝ → ℝ) x) ∧
    (∀ u : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      ∃ v : Distribution (⊤ : Opens ℝ) ℝ ⊤,
        apm_m02j01_IsDistributionalDerivative v u) ∧
    (∀ u v₁ v₂ : Distribution (⊤ : Opens ℝ) ℝ ⊤,
      apm_m02j01_IsDistributionalDerivative v₁ u →
      apm_m02j01_IsDistributionalDerivative v₂ u →
      ∃ c : ℝ, ∀ φ : TestFunction (⊤ : Opens ℝ) ℝ ⊤,
        (v₁ - v₂) φ = c * ∫ x : ℝ, φ x) := by
  /-
  SKIPPED (test-function LF-topology API boundary). The mathematical proof
  needs a continuous linear primitive operator on the codimension-one space of
  compactly supported smooth functions with integral zero. Searches of
  Mathlib's `TestFunction` and `Distribution` APIs found the endpoint identity
  `HasCompactSupport.integral_Ioi_deriv_eq`, but no bundled primitive operator
  that preserves compact support and is continuous for the test-function
  LF topology, nor a theorem that distributional differentiation on `ℝ` is
  surjective with constants as its kernel.

  The pointwise FTC and compact-support argument can establish only the
  underlying function identity. Parts (b) and (c) require bundling that
  construction as a continuous linear map before it can be transposed to a
  `Distribution`; this bridge is not supplied by the abstract distribution
  derivative API. No compiled sibling route was found or reused, and the
  frozen statement was left unchanged.
  -/
  sorry
