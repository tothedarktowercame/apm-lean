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

/-- Mapping an intermediate field of `E` through the canonical embedding
produces an ambient intermediate field below `E`. -/
lemma apm_b98a02_map_subtype_le
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E : IntermediateField F Ω) (A : IntermediateField F E) :
    A.map E.val ≤ E := by
  rw [IntermediateField.map_le_iff_le_comap]
  intro x hx
  exact x.property

/-- The whole extension type maps back onto the ambient intermediate field. -/
lemma apm_b98a02_map_subtype_top
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E : IntermediateField F Ω) :
    (⊤ : IntermediateField F E).map E.val = E := by
  rw [← AlgHom.fieldRange_eq_map, E.fieldRange_val]

/-- Comapping an ambient subfield below `E` and mapping it back recovers it. -/
lemma apm_b98a02_map_comap_subtype
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω]
    (E K : IntermediateField F Ω) (hKE : K ≤ E) :
    (K.comap E.val).map E.val = K := by
  apply IntermediateField.map_comap_eq_self
  rwa [E.fieldRange_val]

lemma apm_b98a02_maximalAbelian_exists
    (F Ω : Type*) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (E : IntermediateField F Ω) [FiniteDimensional F E]
    (hE : IsGalois F E) :
    ∃ A : IntermediateField F Ω,
      apm_b98A02_IsMaximalAbelian F Ω E A := by
  letI : IsGalois F E := hE
  let G := E ≃ₐ[F] E
  let D : Subgroup G := commutator G
  let A₀ : IntermediateField F E := IntermediateField.fixedField D
  let A : IntermediateField F Ω := A₀.map E.val
  haveI : D.Normal := inferInstance
  have hquot : Std.Commutative (· * · : G ⧸ D → G ⧸ D → G ⧸ D) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D)).2 le_rfl
  letI : IsMulCommutative (G ⧸ D) := ⟨hquot⟩
  haveI : IsGalois F A₀ := inferInstance
  let qA := IsGalois.normalAutEquivQuotient D
  haveI : IsMulCommutative (A₀ ≃ₐ[F] A₀) :=
    { is_comm.comm x y := by
        apply qA.symm.injective
        simpa only [map_mul] using hquot.comm (qA.symm x) (qA.symm y) }
  haveI : IsAbelianGalois F A₀ := {}
  let eA : A ≃ₐ[F] A₀ := (IntermediateField.equivMap A₀ E.val).symm
  haveI : IsAbelianGalois F A := IsAbelianGalois.of_algHom eA.toAlgHom
  refine ⟨A, apm_b98a02_map_subtype_le F Ω E A₀, inferInstance,
    (fun σ τ => mul_comm σ τ), ?_⟩
  intro K hKE hKg hKab
  let K₀ : IntermediateField F E := K.comap E.val
  have hmap : K₀.map E.val = K := apm_b98a02_map_comap_subtype F Ω E K hKE
  let eK : K₀ ≃ₐ[F] K := (IntermediateField.equivMap K₀ E.val).trans
    (IntermediateField.equivOfEq hmap)
  letI : IsGalois F K := hKg
  letI : IsMulCommutative (K ≃ₐ[F] K) :=
    { is_comm.comm σ τ := hKab σ τ }
  letI : IsAbelianGalois F K := {}
  letI : IsAbelianGalois F K₀ := IsAbelianGalois.of_algHom eK.toAlgHom
  haveI : K₀.fixingSubgroup.Normal := inferInstance
  let efix : IntermediateField.fixedField K₀.fixingSubgroup ≃ₐ[F] K₀ :=
    IntermediateField.equivOfEq (IsGalois.fixedField_fixingSubgroup K₀)
  letI : IsAbelianGalois F (IntermediateField.fixedField K₀.fixingSubgroup) :=
    IsAbelianGalois.of_algHom efix.toAlgHom
  have hqK : Std.Commutative
      (· * · : G ⧸ K₀.fixingSubgroup → G ⧸ K₀.fixingSubgroup →
        G ⧸ K₀.fixingSubgroup) := by
    let qK := IsGalois.normalAutEquivQuotient K₀.fixingSubgroup
    refine ⟨fun x y => ?_⟩
    apply qK.injective
    simpa only [map_mul] using mul_comm (qK x) (qK y)
  have hDK : D ≤ K₀.fixingSubgroup :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le
      (N := K₀.fixingSubgroup)).1 hqK
  have hK₀A₀ : K₀ ≤ A₀ := (IntermediateField.le_iff_le D K₀).mpr hDK
  rw [← hmap]
  exact IntermediateField.map_mono E.val hK₀A₀

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
  refine ⟨(fun E _ hE => apm_b98a02_maximalAbelian_exists F Ω E hE),
    (fun E _ hE A hA K hKE => apm_b98a02_maximal_iff F Ω E A K hA hKE),
    (fun E L _ _ hE hL => apm_b98a02_isGalois_inf F Ω E L hE hL),
    (fun E L _ _ hE hL A_E A_L A_EL hAE hAL hAEL =>
      apm_b98a02_intersection_maximal_eq F Ω E L A_E A_L A_EL hAE hAL hAEL)⟩
