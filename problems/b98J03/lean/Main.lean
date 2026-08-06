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
  constructor
  · intro hk
    letI := hk
    letI : Finite K := Module.finite_of_finite k
    constructor
    · infer_instance
    · exact Field.exists_primitive_element k K
  constructor
  · intro _ hfin
    letI := Finite.of_finite_univ hfin
    exact Field.exists_primitive_element_of_finite_intermediateField k K ⊤
  constructor
  · intro x hx E
    let p : Polynomial K := (minpoly E x).map (algebraMap E K)
    have hp : IntermediateField.adjoin k (p.coeffs : Set K) = E :=
      IntermediateField.adjoin_minpoly_coeff_of_exists_primitive_element k hx E
    have hsets : IntermediateField.adjoin k
          (Set.range fun n : ℕ => algebraMap E K ((minpoly E x).coeff n)) =
        IntermediateField.adjoin k (p.coeffs : Set K) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        rintro y ⟨n, rfl⟩
        change algebraMap E K ((minpoly E x).coeff n) ∈
          IntermediateField.adjoin k (p.coeffs : Set K)
        rw [show algebraMap E K ((minpoly E x).coeff n) = p.coeff n by
          simp [p]]
        by_cases hn : p.coeff n = 0
        · rw [hn]
          exact (IntermediateField.adjoin k (p.coeffs : Set K)).zero_mem
        · exact IntermediateField.subset_adjoin k (p.coeffs : Set K)
            (by simpa [Polynomial.mem_coeffs_iff] using ⟨n, hn, rfl⟩)
      · rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rw [Finset.mem_coe, Polynomial.mem_coeffs_iff] at hy
        obtain ⟨n, _, rfl⟩ := hy
        exact IntermediateField.subset_adjoin k _ ⟨n, by simp [p]⟩
    exact hsets.trans hp
  · intro hx
    haveI : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
    haveI : Finite (IntermediateField k K) :=
      Field.finite_intermediateField_of_exists_primitive_element k K hx
    exact Set.finite_univ
