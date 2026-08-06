import Mathlib

/-!
# APM b99A03

## Statement repairs

None.

## Encoding questions

A complete finite set of left-coset representatives is encoded by the predicate
`apmLeftTransversal`: its represented cosets are pairwise distinct and cover every
left coset.  The equality with the mapped minimal polynomial simultaneously records
that the conjugate product has coefficients in the image of the base field and that
the corresponding polynomial over the base field is the minimal polynomial.
-/

noncomputable section

def apmLeftCoset {G : Type*} [Group G] (H : Subgroup G) (σ : G) : Set G :=
  {g | σ⁻¹ * g ∈ H}

def apmLeftTransversal {G : Type*} [Group G] [DecidableEq G]
    (H : Subgroup G) (s : Finset G) : Prop :=
  (∀ σ ∈ s, ∀ τ ∈ s, apmLeftCoset H σ = apmLeftCoset H τ → σ = τ) ∧
    ∀ g : G, ∃ σ ∈ s, apmLeftCoset H g = apmLeftCoset H σ

def apmConjugateProduct
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [DecidableEq (E ≃ₐ[F] E)] (α : E) (s : Finset (E ≃ₐ[F] E)) : Polynomial E :=
  ∏ σ ∈ s, (Polynomial.X - Polynomial.C (σ α))

theorem apm_b99a03
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    [DecidableEq (E ≃ₐ[F] E)]
    (α : E) (s : Finset (E ≃ₐ[F] E))
    (hs : apmLeftTransversal
      (IntermediateField.adjoin F {α}).fixingSubgroup s) :
    (∀ σ τ : E ≃ₐ[F] E,
        apmLeftCoset (IntermediateField.adjoin F {α}).fixingSubgroup σ =
            apmLeftCoset (IntermediateField.adjoin F {α}).fixingSubgroup τ ↔
          σ α = τ α) ∧
      (∀ τ : E ≃ₐ[F] E,
        apmLeftTransversal (IntermediateField.adjoin F {α}).fixingSubgroup
          (s.image fun σ => τ * σ)) ∧
      apmConjugateProduct F E α s =
        (minpoly F α).map (algebraMap F E) := by
  sorry
