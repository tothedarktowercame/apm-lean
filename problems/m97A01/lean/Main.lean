import Mathlib

/-!
# APM m97A01: Polar decomposition and compact adjoints

## Statement repairs

None. Although the source says "positive definite", it explicitly defines the
term using the non-strict inequality `⟨Bx,x⟩ ≥ 0`; this is Mathlib's
`ContinuousLinearMap.IsPositive` predicate.

## Encoding questions

The scalar field of the Hilbert space is not printed. We use the standard
complex Hilbert-space formulation. The modulus and adjoint are genuine
continuous linear operators; `Y` is the topological closure of the actual
range of the modulus, and `U : Y → X` is stated with its inclusion map,
factorization, uniqueness, and isometry property.
-/

noncomputable section

def apm_m97A01_modulusRange {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (B : X →L[ℂ] X) : Submodule ℂ X :=
  (LinearMap.range B.toLinearMap).topologicalClosure

def apm_m97A01_isModulus {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A B : X →L[ℂ] X) : Prop :=
  B.IsPositive ∧
  B.comp B = (ContinuousLinearMap.adjoint A).comp A ∧
  (∀ C : X →L[ℂ] X,
    C.IsPositive →
    C.comp C = (ContinuousLinearMap.adjoint A).comp A → C = B) ∧
  ∀ x : X, ‖B x‖ = ‖A x‖

def apm_m97A01_hasPolarFactor {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] (A B : X →L[ℂ] X) : Prop :=
  ∃ inclusion : X →L[ℂ] apm_m97A01_modulusRange B,
    (∀ x : X, (inclusion x).1 = B x) ∧
    ∃ U : apm_m97A01_modulusRange B →L[ℂ] X,
      (∀ x : X, U (inclusion x) = A x) ∧
      (∀ y : apm_m97A01_modulusRange B, ‖U y‖ = ‖y‖) ∧
      ∀ V : apm_m97A01_modulusRange B →L[ℂ] X,
        (∀ x : X, V (inclusion x) = A x) → V = U

theorem apm_m97a01
    (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    (∃ absA : X →L[ℂ] X,
      apm_m97A01_isModulus A absA ∧
      apm_m97A01_hasPolarFactor A absA) ∧
    IsCompactOperator (ContinuousLinearMap.adjoint A) := by
  sorry
