import Mathlib

/-! # APM b98J03: primitive finite field extensions

## Statement repairs

None.
-/

noncomputable section

/-- The four parts of the source: the finite-field case, Steinitz's converse,
recovery of an intermediate field from a minimal polynomial's coefficients,
and finiteness of the intermediate-field lattice of a simple extension. -/
theorem apm_b98j03
    (k K : Type*) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] :
    (Finite k →
      IsCyclic (K ≃ₐ[k] K) ∧
        ∃ x : K, IntermediateField.adjoin k ({x} : Set K) = ⊤) ∧
    (Infinite k → Set.Finite (Set.univ : Set (IntermediateField k K)) →
      ∃ x : K, IntermediateField.adjoin k ({x} : Set K) = ⊤) ∧
    (∀ (x : K), IntermediateField.adjoin k ({x} : Set K) = ⊤ →
      ∀ E : IntermediateField k K,
        IntermediateField.adjoin k
          (Set.range fun n : ℕ =>
            algebraMap E K ((minpoly E x).coeff n)) = E) ∧
    ((∃ x : K, IntermediateField.adjoin k ({x} : Set K) = ⊤) →
      Set.Finite (Set.univ : Set (IntermediateField k K))) := by
  sorry
