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

lemma apm_b98a02_le_of_isMaximalAbelian
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E A K : IntermediateField F Ω)
    (hA : apm_b98A02_IsMaximalAbelian F Ω E A)
    (hKE : K ≤ E) (hK : IsGalois F K)
    (hKab : ∀ σ τ : K ≃ₐ[F] K, σ * τ = τ * σ) :
    K ≤ A :=
  hA.2.2.2 K hKE hK hKab

lemma apm_b98a02_maximalAbelian_unique
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E A B : IntermediateField F Ω)
    (hA : apm_b98A02_IsMaximalAbelian F Ω E A)
    (hB : apm_b98A02_IsMaximalAbelian F Ω E B) : A = B := by
  apply le_antisymm
  · exact apm_b98a02_le_of_isMaximalAbelian F Ω E B A hB
      hA.1 hA.2.1 hA.2.2.1
  · exact apm_b98a02_le_of_isMaximalAbelian F Ω E A B hA
      hB.1 hB.2.1 hB.2.2.1

lemma apm_b98a02_intersection_maximal_le
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E L A_E A_L A_EL : IntermediateField F Ω)
    (hE : apm_b98A02_IsMaximalAbelian F Ω E A_E)
    (hL : apm_b98A02_IsMaximalAbelian F Ω L A_L)
    (hEL : apm_b98A02_IsMaximalAbelian F Ω (E ⊓ L) A_EL) :
    A_EL ≤ A_E ⊓ A_L := by
  apply le_inf
  · exact apm_b98a02_le_of_isMaximalAbelian F Ω E A_E A_EL hE
      (hEL.1.trans inf_le_left) hEL.2.1 hEL.2.2.1
  · exact apm_b98a02_le_of_isMaximalAbelian F Ω L A_L A_EL hL
      (hEL.1.trans inf_le_right) hEL.2.1 hEL.2.2.1

lemma apm_b98a02_isGalois_inf
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (E L : IntermediateField F Ω)
    [FiniteDimensional F E] [FiniteDimensional F L]
    (hE : IsGalois F E) (hL : IsGalois F L) :
    IsGalois F (E ⊓ L : IntermediateField F Ω) := by
  letI : IsGalois F E := hE
  letI : IsGalois F L := hL
  infer_instance

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
  /-
  Boundary (closer hop 1): Mathlib supplies the finite Galois
  correspondence `IsGalois.intermediateFieldEquivSubgroup`, fixed fields, and
  `IntermediateField.normalAutEquivQuotient`. These are the abstract ingredients
  for taking the fixed field of the commutator subgroup.

  The searched API does not package the construction required by this encoding:
  the correspondence produces an intermediate field inside the extension type
  `E`, while `apm_b98A02_IsMaximalAbelian` requires an
  `IntermediateField F Ω` lying below the embedded field `E`. A proof must lift
  that fixed field through `E.subtype`, transport Galoisness and the quotient
  automorphism equivalence across the lift, and prove the universal property
  for arbitrary embedded `K ≤ E`. No commutator-fixed-field theorem or proved
  sibling performs this chain.

  This hop found that the intersection bridge is in fact synthesized by typeclass
  search once the two finite Galois hypotheses and `IsAlgClosure F Ω` are
  installed. `apm_b98a02_isGalois_inf` therefore compiles all of part (c).
  `apm_b98a02_le_of_isMaximalAbelian` extracts the universal property,
  `apm_b98a02_maximalAbelian_unique` proves uniqueness, and
  `apm_b98a02_intersection_maximal_le` proves the forward inclusion
  `A(E ⊓ L) ≤ A(E) ⊓ A(L)` in part (d).

  The remaining reverse inclusion requires proving that an intermediate field
  below an abelian Galois extension is itself Galois with abelian automorphism
  group, then applying maximality. Searches of `LEMMA-INDEX.md`, all solved
  artifacts (including sibling `b93A04`), `ConstructionTargets/`, Mathlib's
  Galois correspondence/fixed-field/restriction APIs, and git history found no
  packaged version matching these embedded intermediate fields. Parts (a) and
  (b) still require lifting the commutator fixed field from inside `E` into
  `Ω` and proving its universal property. The statement appears sound.
  -/
  sorry
