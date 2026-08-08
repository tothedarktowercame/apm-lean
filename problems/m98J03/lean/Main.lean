import Mathlib

/-!
# APM m98J03 — orthogonal projections on a Hilbert space

## Statement repairs

None.

All six parts are included: the spectrum and its two degenerate cases,
compactness, the concrete orthogonal complement and its closedness, invariant
subspaces for commuting operators, and the adjoint.
-/

open Set
open scoped RealInnerProductSpace

noncomputable section

def apm_m98J03_perp {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (V : ClosedSubmodule ℝ H) : Submodule ℝ H :=
  (V : Submodule ℝ H)ᗮ

theorem apm_m98j03 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] [Nontrivial H]
    (V : ClosedSubmodule ℝ H) :
    let P := V.starProjection
    let Vperp := apm_m98J03_perp V
    spectrum ℝ P ⊆ ({0, 1} : Set ℝ) ∧
    (spectrum ℝ P = ({0} : Set ℝ) ↔ V = ⊥) ∧
    (spectrum ℝ P = ({1} : Set ℝ) ↔ V = ⊤) ∧
    (IsCompactOperator P ↔
      FiniteDimensional ℝ (↥(V : Submodule ℝ H))) ∧
    IsClosed (Vperp : Set H) ∧
    (∀ A : H →L[ℝ] H, A.comp P = P.comp A →
      (∀ x ∈ (V : Set H), A x ∈ (V : Set H)) ∧
      (∀ x ∈ (Vperp : Set H), A x ∈ (Vperp : Set H))) ∧
    P.adjoint = P := by
  sorry
