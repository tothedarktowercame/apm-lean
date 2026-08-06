import Mathlib

/-!
# APM b98A02

## Statement repairs

None.

## Encoding questions

All fields in parts (c) and (d) are represented honestly as intermediate fields
inside one algebraic closure `Ω`. The object `A(E)` is specified by its defining
universal property—being the largest abelian Galois intermediate field—rather
than by choosing a construction. Finiteness of the ambient Galois extensions is
recorded by `FiniteDimensional` instances.
-/

noncomputable section

/-- `A` is the largest abelian Galois subextension of `E/F`. -/
def apm_b98A02_IsMaximalAbelian
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E A : IntermediateField F Ω) : Prop :=
  A ≤ E ∧
    IsGalois F A ∧
    (∀ σ τ : A ≃ₐ[F] A, σ * τ = τ * σ) ∧
    ∀ K : IntermediateField F Ω,
      K ≤ E → IsGalois F K →
      (∀ σ τ : K ≃ₐ[F] K, σ * τ = τ * σ) → K ≤ A

theorem apm_b98a02 :
    ∀ (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω],
      (∀ (E : IntermediateField F Ω) [FiniteDimensional F E],
        IsGalois F E →
        ∃ A : IntermediateField F Ω,
          apm_b98A02_IsMaximalAbelian F Ω E A) ∧
      (∀ (E : IntermediateField F Ω) [FiniteDimensional F E],
        IsGalois F E →
        ∀ A : IntermediateField F Ω,
          apm_b98A02_IsMaximalAbelian F Ω E A →
          ∀ K : IntermediateField F Ω, K ≤ E →
            (IsGalois F K ∧ (∀ σ τ : K ≃ₐ[F] K, σ * τ = τ * σ) ↔ K ≤ A)) ∧
      (∀ (E L : IntermediateField F Ω)
        [FiniteDimensional F E] [FiniteDimensional F L],
        IsGalois F E → IsGalois F L →
          IsGalois F (E ⊓ L : IntermediateField F Ω)) ∧
      (∀ (E L : IntermediateField F Ω)
        [FiniteDimensional F E] [FiniteDimensional F L],
        IsGalois F E → IsGalois F L →
        ∀ A_E A_L A_EL : IntermediateField F Ω,
          apm_b98A02_IsMaximalAbelian F Ω E A_E →
          apm_b98A02_IsMaximalAbelian F Ω L A_L →
          apm_b98A02_IsMaximalAbelian F Ω
            (E ⊓ L : IntermediateField F Ω) A_EL →
          A_EL = (A_E ⊓ A_L : IntermediateField F Ω)) := by
  sorry
