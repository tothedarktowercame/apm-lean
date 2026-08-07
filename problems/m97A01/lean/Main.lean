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
    apply (ContinuousLinearMap.nonneg_iff_isPositive P).mpr
    simpa [P] using ContinuousLinearMap.isPositive_adjoint_comp_self A
  refine ⟨B, (ContinuousLinearMap.nonneg_iff_isPositive B).mp
    (CFC.sqrt_nonneg P), ?_, ?_⟩
  · simpa [B, P] using CFC.sqrt_mul_sqrt_self P hP
  · intro C hC hC2
    have hCn : 0 ≤ C :=
      (ContinuousLinearMap.nonneg_iff_isPositive C).mpr hC
    exact (CFC.sqrt_unique (a := P) (b := C)
      (by simpa [P] using hC2) hCn).symm

/-- Positivity and the square identity determine the pointwise norm of the
modulus. -/
lemma apm_m97A01_modulus_norm
    {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A B : X →L[ℂ] X) (hB : B.IsPositive)
    (hB2 : B.comp B = (ContinuousLinearMap.adjoint A).comp A)
    (x : X) : ‖B x‖ = ‖A x‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg (B x)) (norm_nonneg (A x))]
  rw [B.apply_norm_sq_eq_inner_adjoint_left,
    A.apply_norm_sq_eq_inner_adjoint_left]
  rw [hB.isSelfAdjoint.adjoint_eq, hB2]

theorem apm_m97a01
    (X : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X]
    (A : X →L[ℂ] X) (hA : IsCompactOperator A) :
    (∃ absA : X →L[ℂ] X,
      apm_m97A01_isModulus A absA ∧
      apm_m97A01_hasPolarFactor A absA) ∧
    IsCompactOperator (ContinuousLinearMap.adjoint A) := by
  /-
  Closer hop 1 adds `apm_m97A01_modulus_norm`, proving the remaining norm
  clause `‖B x‖ = ‖A x‖` from positivity, self-adjointness, and `B² = A†A`.
  It uses Mathlib's `apply_norm_sq_eq_inner_adjoint_left` and
  `IsPositive.isSelfAdjoint`.  Consequently `apm_m97A01_modulus_core` plus
  this lemma now supplies every field of `apm_m97A01_isModulus`; only the
  polar-factor extension remains in the first conjunct.

  PASS-1 PARTIAL boundary (codex): `apm_m97A01_modulus_core` constructs
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
  development beyond this pass's budget.  Renewed searches covered
  `LEMMA-INDEX.md`, Mathlib's compact-operator, adjoint, extension, projection,
  and compact spectral-theorem sources, `ConstructionTargets`, solved siblings,
  and git history.  No compact-adjoint theorem or codomain-nonsurjective
  isometry extension was found.  The statement is mathematically sound; this
  `sorry` covers precisely those assembly/dependency gaps.
  -/
  sorry
