import Mathlib



/-!
# APM b93A04

## Statement repairs

None. In part (c), the source's subgroup product `H₁H₂` is represented by the
subgroup join `H₁ ⊔ H₂`; under the stated Galois hypotheses these agree.

## Encoding questions

None. The compositum and intersection are the join and meet in Mathlib's
lattice of intermediate fields.
-/

open scoped BigOperators

theorem apm_b93a04 :
    ∀ (F K : Type*) [Field F] [Field K] [Algebra F K] [CharZero F]
        [FiniteDimensional F K] (L₁ L₂ : IntermediateField F K),
      (∀ x : K,
        x ∈ L₁ ⊔ L₂ ↔
          ∃ (n : ℕ) (a : Fin n → L₁) (b : Fin n → L₂),
            x = ∑ i, (a i : K) * (b i : K)) ∧
      (IsGalois F L₁ → IsGalois F L₂ → IsGalois F ↥(L₁ ⊔ L₂)) ∧
      (IsGalois F K →
        (L₁ ⊔ L₂).fixingSubgroup = L₁.fixingSubgroup ⊓ L₂.fixingSubgroup ∧
        (L₁ ⊓ L₂).fixingSubgroup = L₁.fixingSubgroup ⊔ L₂.fixingSubgroup) ∧
      (L₁ ⊔ L₂ = ⊤ →
        IsGalois F L₁ → IsGalois F L₂ →
        (∀ σ τ : L₁ ≃ₐ[F] L₁, σ * τ = τ * σ) →
        (∀ σ τ : L₂ ≃ₐ[F] L₂, σ * τ = τ * σ) →
        IsGalois F K ∧ ∀ σ τ : K ≃ₐ[F] K, σ * τ = τ * σ) := by
  intro F K _ _ _ _ _ L₁ L₂
  have hsumProducts_le : ∀ x : K,
      (∃ (n : ℕ) (a : Fin n → L₁) (b : Fin n → L₂),
        x = ∑ i, (a i : K) * (b i : K)) → x ∈ L₁ ⊔ L₂ := by
    intro x
    rintro ⟨n, a, b, rfl⟩
    refine Submodule.sum_mem (L₁ ⊔ L₂).toSubmodule ?_
    intro i hi
    exact (L₁ ⊔ L₂).mul_mem
      ((show L₁ ≤ L₁ ⊔ L₂ from le_sup_left) (a i).property)
      ((show L₂ ≤ L₁ ⊔ L₂ from le_sup_right) (b i).property)
  have hfixingSup :
      (L₁ ⊔ L₂).fixingSubgroup =
        L₁.fixingSubgroup ⊓ L₂.fixingSubgroup :=
    IntermediateField.fixingSubgroup_sup
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    constructor
    · /- PASS-1 boundary: the reverse finite-sum description requires showing
         the span of products from `L₁` and `L₂` is inverse-closed.  I searched
         `IntermediateField.exists_finset_of_mem_supr'`, subalgebra product
         APIs, and finite-dimensional-domain-to-field instances.  The intended
         local route is to construct this span as a finite-dimensional
         subalgebra/domain, then obtain inverses by injective-implies-surjective
         multiplication.  No packaged lemma returned the displayed `Fin n`
         normal form directly. -/
      sorry
    · exact hsumProducts_le x
  · intro h1 h2
    letI : IsGalois F L₁ := h1
    letI : IsGalois F L₂ := h2
    infer_instance
  · intro hK
    letI : IsGalois F K := hK
    refine ⟨hfixingSup, ?_⟩
    have hdual := (IsGalois.intermediateFieldEquivSubgroup (F := F) (E := K)).map_inf L₁ L₂
    exact congrArg OrderDual.ofDual hdual
  · /- PASS-1 boundary: `IsGalois.sup_right`/instances now close Galoisness
       of the compositum, and the order-dual Galois correspondence closes both
       fixing-subgroup lattice identities.  For the last abelianity claim I
       searched `IntermediateField.restrictRestrictAlgEquivMapHom_injective`,
       restriction homomorphisms, and commutative-range lemmas.  The remaining
       bridge is to combine the two restriction maps into an injective map
       `Gal(K/F) → Gal(L₁/F) × Gal(L₂/F)` under `L₁ ⊔ L₂ = ⊤`, then pull
       commutativity back from the product. -/
    sorry
