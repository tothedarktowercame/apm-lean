import Mathlib

/-! # APM m99A03: compact powers and normal nilpotent operators

## Statement repairs

Part (b) cannot hold on every Hilbert space (for example, not on a
finite-dimensional one).  Its instruction to “construct an example” is encoded
as an existential example on the explicit infinite-dimensional Hilbert space
`m99A03ExampleSpace`.
-/

noncomputable section

abbrev m99A03L2 := lp (fun _ : ℕ => ℂ) 2
abbrev m99A03ExampleSpace := m99A03L2 × m99A03L2 × m99A03L2

theorem apm_m99a03 :
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (A : H →L[ℂ] H),
      IsCompactOperator A → IsStarNormal A → A ^ 3 = 0 → A = 0) ∧
    (∃ A : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace,
      ¬IsCompactOperator A ∧
      ¬IsCompactOperator
        ((A ^ 2 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace) ∧
      IsCompactOperator
        ((A ^ 3 : m99A03ExampleSpace →L[ℂ] m99A03ExampleSpace) :
          m99A03ExampleSpace → m99A03ExampleSpace)) := by
  sorry
