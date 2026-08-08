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

/-- Intersection compatibility follows because Mathlib's
`IsAbelianGalois.of_algHom` transports abelian Galois structure to every
embedded subextension. -/
lemma apm_b98a02_intersection_maximal_eq
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (E L A_E A_L A_EL : IntermediateField F Ω)
    [FiniteDimensional F E] [FiniteDimensional F L]
    (hAE : apm_b98A02_IsMaximalAbelian F Ω E A_E)
    (hAL : apm_b98A02_IsMaximalAbelian F Ω L A_L)
    (hAEL : apm_b98A02_IsMaximalAbelian F Ω (E ⊓ L) A_EL) :
    A_EL = (A_E ⊓ A_L : IntermediateField F Ω) := by
  apply le_antisymm
  · exact apm_b98a02_intersection_maximal_le F Ω E L A_E A_L A_EL hAE hAL hAEL
  · letI : IsGalois F A_E := hAE.2.1
    letI : IsMulCommutative (A_E ≃ₐ[F] A_E) :=
      { is_comm.comm σ τ := hAE.2.2.1 σ τ }
    letI : IsAbelianGalois F A_E := { }
    let K : IntermediateField F Ω := A_E ⊓ A_L
    have hKAE : K ≤ A_E := inf_le_left
    let f : K →ₐ[F] A_E := IntermediateField.inclusion hKAE
    letI : IsAbelianGalois F K := IsAbelianGalois.of_algHom f
    apply apm_b98a02_le_of_isMaximalAbelian F Ω (E ⊓ L) A_EL K hAEL
    · exact le_inf (inf_le_left.trans hAE.1) (inf_le_right.trans hAL.1)
    · infer_instance
    · exact fun σ τ => mul_comm σ τ

/-- The universal property is an iff: the reverse direction again uses
`IsAbelianGalois.of_algHom` for the inclusion into the maximal abelian field. -/
lemma apm_b98a02_maximal_iff
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E A K : IntermediateField F Ω)
    (hA : apm_b98A02_IsMaximalAbelian F Ω E A) (hKE : K ≤ E) :
    (IsGalois F K ∧ (∀ σ τ : K ≃ₐ[F] K, σ * τ = τ * σ) ↔ K ≤ A) := by
  constructor
  · rintro ⟨hK, hKab⟩
    exact apm_b98a02_le_of_isMaximalAbelian F Ω E A K hA hKE hK hKab
  · intro hKA
    letI : IsGalois F A := hA.2.1
    letI : IsMulCommutative (A ≃ₐ[F] A) :=
      { is_comm.comm σ τ := hA.2.2.1 σ τ }
    letI : IsAbelianGalois F A := { }
    let f : K →ₐ[F] A := IntermediateField.inclusion hKA
    letI : IsAbelianGalois F K := IsAbelianGalois.of_algHom f
    exact ⟨inferInstance, fun σ τ => mul_comm σ τ⟩

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
  intro F Ω _ _ _ _
  refine ⟨?_,
    (fun E _ hE A hA K hKE => apm_b98a02_maximal_iff F Ω E A K hA hKE),
    (fun E L _ _ hE hL => apm_b98a02_isGalois_inf F Ω E L hE hL),
    (fun E L _ _ hE hL A_E A_L A_EL hAE hAL hAEL =>
      apm_b98a02_intersection_maximal_eq F Ω E L A_E A_L A_EL hAE hAL hAEL)⟩
  /-
  Boundary (closer hop 2): parts (b), (c), and (d) are now fully assembled in
  the main proof. Inspection of the newer
  `Mathlib.FieldTheory.Galois.Abelian` API found the previously missed class
  `IsAbelianGalois` and, decisively, `IsAbelianGalois.of_algHom`. The compiled
  helper `apm_b98a02_maximal_iff` uses it to prove that every embedded field
  below `A` is abelian Galois, closing the reverse implication in part (b).
  `apm_b98a02_intersection_maximal_eq` applies the same theorem to the inclusion
  `A_E ⊓ A_L → A_E`, then maximality closes the reverse inclusion in part (d).
  Part (c) continues to use the compiled typeclass proof
  `apm_b98a02_isGalois_inf`.

  Only part (a) remains. The finite Galois correspondence
  `IsGalois.intermediateFieldEquivSubgroup`, fixed fields, and
  `IntermediateField.normalAutEquivQuotient` provide the abstract ingredients
  for the commutator fixed field, but do not package the construction required
  by this encoding:
  the correspondence produces an intermediate field inside the extension type
  `E`, while `apm_b98A02_IsMaximalAbelian` requires an
  `IntermediateField F Ω` lying below the embedded field `E`. A proof must lift
  that fixed field through `E.subtype`, transport Galoisness and the quotient
  automorphism equivalence across the lift, and prove the universal property
  for arbitrary embedded `K ≤ E`. No commutator-fixed-field theorem or proved
  sibling performs this chain.

  that fixed field through `E.subtype`, transport Galoisness and the quotient
  automorphism equivalence across the lift, and prove its universal property
  for arbitrary embedded `K ≤ E`. No closed artifact or construction module
  performs that remaining chain. The statement is unchanged and appears sound.
  -/
  all_goals sorry
