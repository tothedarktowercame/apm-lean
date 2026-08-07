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

/-- The continuous functional calculus supplies the unique positive square
root of `A†A`. -/
lemma apm_m97A01_modulus_core
    (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) :
    ∃ B : X →L[ℂ] X,
      B.IsPositive ∧
      B.comp B = (ContinuousLinearMap.adjoint A).comp A ∧
      ∀ C : X →L[ℂ] X,
        C.IsPositive →
        C.comp C = (ContinuousLinearMap.adjoint A).comp A → C = B := by
  let P : X →L[ℂ] X := (ContinuousLinearMap.adjoint A).comp A
  let B : X →L[ℂ] X := CFC.sqrt P
  have hP : 0 ≤ P := by
    rw [show P = star A * A by
      simp [P, ContinuousLinearMap.star_eq_adjoint]]
    exact star_mul_self_nonneg A
  refine ⟨B, (ContinuousLinearMap.nonneg_iff_isPositive B).mp
    (CFC.sqrt_nonneg P), ?_, ?_⟩
  · simpa [B, P] using CFC.sqrt_mul_sqrt_self P hP
  · intro C hC hC2
    have hCn : 0 ≤ C :=
      (ContinuousLinearMap.nonneg_iff_isPositive C).mpr hC
    exact (CFC.sqrt_unique (a := P) (b := C)
      (by simpa [P] using hC2) hCn).symm

theorem apm_m97a01
    (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    (∃ absA : X →L[ℂ] X,
      apm_m97A01_isModulus A absA ∧
      apm_m97A01_hasPolarFactor A absA) ∧
    IsCompactOperator (ContinuousLinearMap.adjoint A) := by
  /-
  PASS-1 PARTIAL boundary (codex): `apm_m97A01_modulus_core` now constructs
  the modulus as `CFC.sqrt ((ContinuousLinearMap.adjoint A).comp A)` and
  proves its positivity, square identity, and uniqueness using
  `CFC.sqrt_nonneg`, `CFC.sqrt_mul_sqrt_self`, and `CFC.sqrt_unique`.
  Searches of
  `Mathlib/Analysis/Normed/Operator/Compact.lean`, the CFC rpow files, the
  closed sibling artifacts, `ConstructionTargets/`, and `YoungL2.lean` did
  not locate either of the two remaining packaged Hilbert-space results:

  * extension of the densely defined isometry `absA x ↦ A x` from the
    closure of `range absA` with exactly the stated codomain and uniqueness;
  * compactness of `ContinuousLinearMap.adjoint A` from `IsCompactOperator A`.

  `LinearEquiv.extendOfIsometry` was also checked, but requires dense range in
  the target and therefore does not apply to the polar factor here.  Proving
  both results locally would require a substantial Hilbert-space approximation
  development beyond this pass's budget.  The statement is mathematically
  sound; this `sorry` covers precisely those assembly/dependency gaps.
  -/
  sorry
