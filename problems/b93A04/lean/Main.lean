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
    · intro hx
      -- Mathlib's tensor-product range theorem supplies the finite-sum normal form.
      let g := Algebra.TensorProduct.productMap L₁.val L₂.val
      have hrange : g.range = (L₁ ⊔ L₂).toSubalgebra := by
        rw [Algebra.TensorProduct.productMap_range, L₁.range_val, L₂.range_val,
          IntermediateField.sup_toSubalgebra_of_left]
      have hxrange : x ∈ g.range := by rwa [hrange]
      obtain ⟨t, rfl⟩ := hxrange
      obtain ⟨n, a, b, ht⟩ := TensorProduct.exists_sum_tmul_eq t
      refine ⟨n, a, b, ?_⟩
      rw [ht, map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rfl
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
  · intro htop h1 h2 hab1 hab2
    letI : IsGalois F L₁ := h1
    letI : IsGalois F L₂ := h2
    have hgalK : IsGalois F K := by
      rw [← isGalois_iff_isGalois_top, ← htop]
      infer_instance
    letI : IsGalois F K := hgalK
    let r₁ := AlgEquiv.restrictNormalHom (F := F) (K₁ := K) L₁
    let r₂ := AlgEquiv.restrictNormalHom (F := F) (K₁ := K) L₂
    -- The product restriction map has kernel equal to the fixing subgroup of the sup.
    have hinj : Function.Injective (r₁.prod r₂) := by
      rw [← MonoidHom.ker_eq_bot_iff, MonoidHom.ker_prod,
        IntermediateField.restrictNormalHom_ker,
        IntermediateField.restrictNormalHom_ker, ← hfixingSup, htop,
        IntermediateField.fixingSubgroup_top]
    refine ⟨hgalK, ?_⟩
    intro σ τ
    apply hinj
    simp only [map_mul]
    apply Prod.ext
    · exact hab1 (r₁ σ) (r₁ τ)
    · exact hab2 (r₂ σ) (r₂ τ)
