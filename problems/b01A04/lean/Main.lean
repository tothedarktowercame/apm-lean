import Mathlib

/-!
# APM b01A04: Realizing groups as Galois groups over ℚ

## Statement repairs

None.

## Encoding questions

None. A field extension is existentially bundled with its field and
`ℚ`-algebra structures. Its Galois group is the full group of
`ℚ`-algebra automorphisms. `Multiplicative` converts the additive groups
`ZMod 3` and `ZMod 3 × ZMod 3` to the multiplicative convention used by
automorphism groups.
-/

noncomputable section

/-- A group `G` occurs as the Galois group of some field extension of `ℚ`. -/
def apm_b01A04_isGaloisGroup (G : Type) [Group G] : Prop :=
  ∃ K : Type,
    ∃ hK : Field K,
      letI := hK
      ∃ hA : Algebra ℚ K,
        letI := hA
        IsGalois ℚ K ∧ Nonempty ((K ≃ₐ[ℚ] K) ≃* G)

/-- Realizability is invariant under group isomorphism. This allows later
constructions to use whichever concrete model of the order-three groups is
most convenient. -/
lemma apm_b01A04_isGaloisGroup_of_mulEquiv
    {G H : Type} [Group G] [Group H]
    (hG : apm_b01A04_isGaloisGroup G) (e : G ≃* H) :
    apm_b01A04_isGaloisGroup H := by
  rcases hG with ⟨K, hK, hA, hGal, ⟨g⟩⟩
  exact ⟨K, hK, hA, hGal, ⟨g.trans e⟩⟩

/-- The additive product convention in the statement is interchangeable with
the product of the two multiplicative group models.  This is the codomain
needed by the standard restriction map from a compositum's automorphism group. -/
lemma apm_b01A04_isGaloisGroup_multiplicative_prod_iff
    (A B : Type) [AddGroup A] [AddGroup B] :
    apm_b01A04_isGaloisGroup (Multiplicative (A × B)) ↔
      apm_b01A04_isGaloisGroup (Multiplicative A × Multiplicative B) := by
  constructor
  · intro h
    exact apm_b01A04_isGaloisGroup_of_mulEquiv h (MulEquiv.prodMultiplicative A B)
  · intro h
    exact apm_b01A04_isGaloisGroup_of_mulEquiv h (MulEquiv.prodMultiplicative A B).symm

/-- A degree-three Galois extension has exactly the cyclic group requested in
the first conjunct.  This isolates the remaining arithmetic task from the
finite-group identification: `IsGalois.card_aut_eq_finrank` gives order three,
and Mathlib's prime-cardinality classification supplies the isomorphism. -/
lemma apm_b01A04_aut_mulEquiv_zmod_three
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hfin : Module.finrank ℚ K = 3) :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 3)) := by
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 3 := by
    rw [IsGalois.card_aut_eq_finrank, hfin]
  exact ⟨mulEquivOfPrimeCardEq hcard (by simp)⟩

/-- Why this unblocks `apm_b01a04`: this is the missing arithmetic
construction of two linearly disjoint cyclic cubic extensions inside their
degree-nine compositum. Either intermediate field supplies the first witness,
while the pair supplies the input for the product restriction theorem. -/
theorem apm_b01A04_bridge_cubic_compositum_exists :
    ∃ E : Type,
      ∃ hE : Field E,
        letI := hE
        ∃ hA : Algebra ℚ E,
          letI := hA
          ∃ hfd : FiniteDimensional ℚ E,
            letI := hfd
            ∃ K L : IntermediateField ℚ E,
              IsGalois ℚ E ∧
              IsGalois ℚ K ∧
              IsGalois ℚ L ∧
              Module.finrank ℚ K = 3 ∧
              Module.finrank ℚ L = 3 ∧
              K ⊓ L = ⊥ ∧
              K ⊔ L = ⊤ := by
  sorry

/-- Why this unblocks `apm_b01a04`: this is the simultaneous restriction
equivalence for a compositum. The intersection hypothesis gives surjectivity
onto both compatible factor automorphisms, and the join hypothesis gives
injectivity; applying the cubic identification to both factors yields the
requested product of two copies of `ZMod 3`. -/
theorem apm_b01A04_bridge_compositum_restrict_equiv
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]
    (K L : IntermediateField F E)
    (hK : IsGalois F K) (hL : IsGalois F L)
    (hinf : K ⊓ L = ⊥) (hsup : K ⊔ L = ⊤) :
    Nonempty
      ((E ≃ₐ[F] E) ≃* ((K ≃ₐ[F] K) × (L ≃ₐ[F] L))) := by
  let rK : (E ≃ₐ[F] E) →* (K ≃ₐ[F] K) := AlgEquiv.restrictNormalHom K
  let rL : (E ≃ₐ[F] E) →* (L ≃ₐ[F] L) := AlgEquiv.restrictNormalHom L
  let r := rK.prod rL
  refine ⟨MulEquiv.ofBijective r ?_⟩
  apply (Nat.bijective_iff_injective_and_card r).2
  constructor
  · refine (injective_iff_map_eq_one r).2 fun φ hφ ↦ ?_
    have hfixK : φ ∈ K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' := DFunLike.congr_fun (congr_arg Prod.fst hφ) (⟨x, hx⟩ : K)
      simpa [r, rK, AlgEquiv.restrictNormalHom_apply] using congr_arg Subtype.val hx'
    have hfixL : φ ∈ L.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hx' := DFunLike.congr_fun (congr_arg Prod.snd hφ) (⟨x, hx⟩ : L)
      simpa [r, rL, AlgEquiv.restrictNormalHom_apply] using congr_arg Subtype.val hx'
    have hfix : φ ∈ (K ⊔ L).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hfixK, hfixL⟩
    rw [hsup, IntermediateField.fixingSubgroup_top] at hfix
    exact hfix
  · rw [Nat.card_prod, IsGalois.card_aut_eq_finrank,
      IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank]
    have hdisj : K.LinearDisjoint L :=
      IntermediateField.LinearDisjoint.of_inf_eq_bot hinf
    rw [← hdisj.finrank_sup, hsup, IntermediateField.finrank_top']

theorem apm_b01a04 :
    apm_b01A04_isGaloisGroup (Multiplicative (ZMod 3)) ∧
      apm_b01A04_isGaloisGroup
        (Multiplicative (ZMod 3 × ZMod 3)) := by
  /-
  PARTIAL boundary (closer hop 2): realizability transport across an arbitrary
  group isomorphism is now compiled as
  `apm_b01A04_isGaloisGroup_of_mulEquiv`. This removes a recurring model
  mismatch between additive `ZMod`, alternating groups, cyclotomic unit
  groups, and automorphism groups.

  Closer hop 2 additionally compiles
  `apm_b01A04_isGaloisGroup_multiplicative_prod_iff`, removing the precise
  codomain mismatch between the frozen `Multiplicative (ZMod 3 × ZMod 3)` and
  the product of automorphism groups delivered by a compositum restriction
  map. Inspection of `FieldTheory/Galois/Basic.lean` found the usable maps
  `IntermediateField.restrictRestrictAlgEquivMapHom` together with injectivity
  from `K ⊔ L = ⊤` and surjectivity from `K ⊓ L = ⊥`; and
  `FieldTheory/LinearDisjoint.lean` uses exactly these two results to obtain
  the corresponding automorphism-cardinality equivalence. They do not,
  however, construct the required pair of rational cyclic cubic subfields or
  package the simultaneous product restriction isomorphism.

  I searched Mathlib's cyclotomic and Galois-correspondence sources. They
  provide cyclotomic Galois extensions and automorphism embeddings, but no
  ready theorem identifying the maximal real cubic subfield of `ℚ(ζ₇)` or
  constructing the linearly disjoint compositum of the `7`- and `9`-cyclotomic
  cubic subfields. The explicit-polynomial route likewise still requires the
  assembled theorem “irreducible cubic with square discriminant has cyclic
  order-three Galois group.” Thus construction of the first witness remains
  open; the product witness additionally requires compositum Galois-group
  transport and linear disjointness.

  CLOSER HOP 3: `apm_b01A04_aut_mulEquiv_zmod_three` now removes the group-
  identification half of the explicit-polynomial route. For any finite-
  dimensional degree-three Galois extension it combines
  `IsGalois.card_aut_eq_finrank` with `mulEquivOfPrimeCardEq`, yielding exactly
  the frozen `Multiplicative (ZMod 3)` model. Consequently no separate
  classification of the resulting order-three group is needed after
  Galoisness is established. Searches of the cyclic-group API, Galois
  cardinality API, cyclotomic sources, and prior compositum sources still
  produced no actual rational degree-three Galois field or a linearly
  disjoint pair. Those arithmetic constructions and the simultaneous
  restriction equivalence for the compositum remain open.
  -/
  rcases apm_b01A04_bridge_cubic_compositum_exists with ⟨E, hE, hrest⟩
  letI : Field E := hE
  rcases hrest with ⟨hA, hrest⟩
  letI : Algebra ℚ E := hA
  rcases hrest with ⟨hfd, K, L, hGalE, hGalK, hGalL, hfinK, hfinL, hinf, hsup⟩
  letI : FiniteDimensional ℚ E := hfd
  have hAlgK : (DivisionRing.toRatAlgebra : Algebra ℚ K) = K.algebra' := Subsingleton.elim _ _
  have hAlgL : (DivisionRing.toRatAlgebra : Algebra ℚ L) = L.algebra' := Subsingleton.elim _ _
  have hGalK' : @IsGalois ℚ _ K _ K.algebra' := hAlgK ▸ hGalK
  have hGalL' : @IsGalois ℚ _ L _ L.algebra' := hAlgL ▸ hGalL
  letI : Algebra ℚ K := K.algebra'
  letI : Algebra ℚ L := L.algebra'
  have hfinK' : Module.finrank ℚ K = 3 := by simpa [← hAlgK] using hfinK
  have hfinL' : Module.finrank ℚ L = 3 := by simpa [← hAlgL] using hfinL
  have eK := apm_b01A04_aut_mulEquiv_zmod_three K hfinK'
  have eL := apm_b01A04_aut_mulEquiv_zmod_three L hfinL'
  constructor
  · exact ⟨K, inferInstance, inferInstance, hGalK', eK⟩
  · have eProd := apm_b01A04_bridge_compositum_restrict_equiv
      ℚ E K L hGalK' hGalL' hinf hsup
    have hprod : apm_b01A04_isGaloisGroup
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) := by
      rcases eK with ⟨eK⟩
      rcases eL with ⟨eL⟩
      rcases eProd with ⟨eProd⟩
      exact ⟨E, hE, hA, hGalE, ⟨eProd.trans (eK.prodCongr eL)⟩⟩
    exact (apm_b01A04_isGaloisGroup_multiplicative_prod_iff (ZMod 3) (ZMod 3)).2 hprod
