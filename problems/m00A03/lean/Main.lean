import Mathlib

/-!
# APM m00A03: Riesz's lemma and compact-operator spectra

## Statement repairs

None.

## Encoding questions

The scalar field of the Banach space is not printed. Because part (b) discusses
the complex spectrum using `z` and `|z|`, we use the standard complex Banach
space formulation. No central object is omitted: the conclusion concerns
Mathlib's algebraic spectrum of the continuous linear operator itself.
-/

open Set Metric

noncomputable section

theorem apm_m00a03
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X]
    [CompleteSpace X] :
    (∀ (Y Z : Submodule ℂ X),
      Y ≤ Z → Y ≠ Z → IsClosed (Y : Set X) →
        ∃ z ∈ Z, ‖z‖ = 1 ∧ (1 / 2 : ℝ) ≤ infDist z (Y : Set X)) ∧
    ∀ A : X →L[ℂ] X, IsCompactOperator A →
      (∀ ε : ℝ, 0 < ε →
        {z ∈ spectrum ℂ A | ε < ‖z‖}.Finite) ∧
      derivedSet (spectrum ℂ A) ⊆ {0} := by
  sorry
