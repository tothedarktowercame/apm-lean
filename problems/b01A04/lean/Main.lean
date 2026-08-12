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

private abbrev apm_b01A04_U7 := (ZMod 7)ˣ
private abbrev apm_b01A04_U9 := (ZMod 9)ˣ

private def apm_b01A04_conj7 : Subgroup apm_b01A04_U7 := Subgroup.zpowers (-1)
private def apm_b01A04_conj9 : Subgroup apm_b01A04_U9 := Subgroup.zpowers (-1)

private lemma apm_b01A04_card_conj7 : Nat.card apm_b01A04_conj7 = 2 := by
  letI : NeZero 7 := ⟨by norm_num⟩
  letI : Fact (1 < 7) := ⟨by norm_num⟩
  unfold apm_b01A04_conj7
  rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one,
    ringChar.eq (ZMod 7) 7]
  norm_num

private lemma apm_b01A04_card_conj9 : Nat.card apm_b01A04_conj9 = 2 := by
  letI : NeZero 9 := ⟨by norm_num⟩
  letI : Fact (1 < 9) := ⟨by norm_num⟩
  unfold apm_b01A04_conj9
  rw [Nat.card_zpowers, ← orderOf_units, Units.val_neg, Units.val_one, orderOf_neg_one,
    ringChar.eq (ZMod 9) 9]
  norm_num

private lemma apm_b01A04_cyclotomic_subgroup_inf :
    (apm_b01A04_conj7.prod (⊤ : Subgroup apm_b01A04_U9)) ⊓
        ((⊤ : Subgroup apm_b01A04_U7).prod apm_b01A04_conj9) =
      apm_b01A04_conj7.prod apm_b01A04_conj9 := by
  ext x
  simp only [Subgroup.mem_inf, Subgroup.mem_prod, Subgroup.mem_top, and_true, true_and]

private lemma apm_b01A04_cyclotomic_subgroup_sup :
    (apm_b01A04_conj7.prod (⊤ : Subgroup apm_b01A04_U9)) ⊔
        ((⊤ : Subgroup apm_b01A04_U7).prod apm_b01A04_conj9) = ⊤ := by
  apply top_unique
  rintro ⟨x, y⟩ -
  have hx : (x, 1) ∈
      (apm_b01A04_conj7.prod (⊤ : Subgroup apm_b01A04_U9)) ⊔
        ((⊤ : Subgroup apm_b01A04_U7).prod apm_b01A04_conj9) := by
    apply Subgroup.mem_sup_right
    simp [Subgroup.mem_prod]
  have hy : (1, y) ∈
      (apm_b01A04_conj7.prod (⊤ : Subgroup apm_b01A04_U9)) ⊔
        ((⊤ : Subgroup apm_b01A04_U7).prod apm_b01A04_conj9) := by
    apply Subgroup.mem_sup_left
    simp [Subgroup.mem_prod]
  simpa using (Subgroup.mul_mem _ hx hy)

private lemma apm_b01A04_card_cyclotomic_subgroups :
    Nat.card (apm_b01A04_conj7.prod apm_b01A04_conj9) = 4 ∧
      Nat.card (apm_b01A04_conj7.prod (⊤ : Subgroup apm_b01A04_U9)) = 12 ∧
      Nat.card ((⊤ : Subgroup apm_b01A04_U7).prod apm_b01A04_conj9) = 12 := by
  letI : NeZero 7 := ⟨by norm_num⟩
  letI : NeZero 9 := ⟨by norm_num⟩
  simp only [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    apm_b01A04_card_conj7, apm_b01A04_card_conj9, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  constructor
  · norm_num
  constructor
  · rw [show Nat.totient 9 = 6 by
      rw [show 9 = 3 ^ 2 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
      norm_num]
  · rw [show Nat.totient 7 = 6 by rw [Nat.totient_prime (by norm_num)]]

set_option maxHeartbeats 800000

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
  let C := CyclotomicField 63 ℚ
  letI : NeZero 63 := ⟨by norm_num⟩
  letI : NeZero (63 : ℚ) := ⟨by norm_num⟩
  letI : IsCyclotomicExtension {63} ℚ C := CyclotomicField.isCyclotomicExtension 63 ℚ
  letI : NumberField C := IsCyclotomicExtension.numberField {63} ℚ C
  letI : FiniteDimensional ℚ C := IsCyclotomicExtension.finiteDimensional {63} ℚ C
  letI : IsGalois ℚ C := IsCyclotomicExtension.isGalois {63} ℚ C
  letI : IsAbelianGalois ℚ C := IsCyclotomicExtension.isAbelianGalois {63} ℚ C
  let eCRT : (ZMod 63)ˣ ≃* apm_b01A04_U7 × apm_b01A04_U9 :=
    (Units.mapEquiv (ZMod.chineseRemainder (show Nat.Coprime 7 9 by norm_num)).toMulEquiv).trans
      MulEquiv.prodUnits
  let eG : (C ≃ₐ[ℚ] C) ≃* apm_b01A04_U7 × apm_b01A04_U9 :=
    (IsCyclotomicExtension.Rat.galEquivZMod 63 C).trans eCRT
  let P0 := apm_b01A04_conj7.prod apm_b01A04_conj9
  let P1 := apm_b01A04_conj7.prod (⊤ : Subgroup apm_b01A04_U9)
  let P2 := (⊤ : Subgroup apm_b01A04_U7).prod apm_b01A04_conj9
  let H0 : Subgroup (C ≃ₐ[ℚ] C) := eG.comapSubgroup P0
  let H1 : Subgroup (C ≃ₐ[ℚ] C) := eG.comapSubgroup P1
  let H2 : Subgroup (C ≃ₐ[ℚ] C) := eG.comapSubgroup P2
  let E0 : IntermediateField ℚ C := IntermediateField.fixedField H0
  let F1 : IntermediateField ℚ C := IntermediateField.fixedField H1
  let F2 : IntermediateField ℚ C := IntermediateField.fixedField H2
  have h01 : H0 ≤ H1 := by
    apply eG.comapSubgroup.monotone
    intro x hx
    exact ⟨hx.1, Subgroup.mem_top _⟩
  have h02 : H0 ≤ H2 := by
    apply eG.comapSubgroup.monotone
    intro x hx
    exact ⟨Subgroup.mem_top _, hx.2⟩
  have hF1 : F1 ≤ E0 := IntermediateField.fixedField_le h01
  have hF2 : F2 ≤ E0 := IntermediateField.fixedField_le h02
  let K : IntermediateField ℚ E0 := IntermediateField.restrict hF1
  let L : IntermediateField ℚ E0 := IntermediateField.restrict hF2
  have hcardH0 : Nat.card H0 = 4 := by
    calc
      Nat.card H0 = Nat.card P0 := by
        symm
        rw [show H0 = Subgroup.map (eG.symm : _ →* _) P0 by
          exact Subgroup.comap_equiv_eq_map_symm eG P0]
        exact Nat.card_congr (eG.symm.subgroupMap P0).toEquiv
      _ = 4 := apm_b01A04_card_cyclotomic_subgroups.1
  have hcardH1 : Nat.card H1 = 12 := by
    calc
      Nat.card H1 = Nat.card P1 := by
        symm
        rw [show H1 = Subgroup.map (eG.symm : _ →* _) P1 by
          exact Subgroup.comap_equiv_eq_map_symm eG P1]
        exact Nat.card_congr (eG.symm.subgroupMap P1).toEquiv
      _ = 12 := apm_b01A04_card_cyclotomic_subgroups.2.1
  have hcardH2 : Nat.card H2 = 12 := by
    calc
      Nat.card H2 = Nat.card P2 := by
        symm
        rw [show H2 = Subgroup.map (eG.symm : _ →* _) P2 by
          exact Subgroup.comap_equiv_eq_map_symm eG P2]
        exact Nat.card_congr (eG.symm.subgroupMap P2).toEquiv
      _ = 12 := apm_b01A04_card_cyclotomic_subgroups.2.2
  have hfinC : Module.finrank ℚ C = 36 := by
    rw [IsCyclotomicExtension.finrank (n := 63) C
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    rw [show 63 = 7 * 9 by norm_num, Nat.totient_mul (by norm_num)]
    rw [Nat.totient_prime (by norm_num), show Nat.totient 9 = 6 by
      rw [show 9 = 3 ^ 2 by norm_num, Nat.totient_prime_pow (by norm_num) (by norm_num)]
      norm_num]
  have hfinE : Module.finrank ℚ E0 = 9 := by
    have ht := Module.finrank_mul_finrank ℚ E0 C
    rw [IntermediateField.finrank_fixedField_eq_card H0, hcardH0, hfinC] at ht
    omega
  have hfinF1 : Module.finrank ℚ F1 = 3 := by
    have ht := Module.finrank_mul_finrank ℚ F1 C
    rw [IntermediateField.finrank_fixedField_eq_card H1, hcardH1, hfinC] at ht
    omega
  have hfinF2 : Module.finrank ℚ F2 = 3 := by
    have ht := Module.finrank_mul_finrank ℚ F2 C
    rw [IntermediateField.finrank_fixedField_eq_card H2, hcardH2, hfinC] at ht
    omega
  letI : FiniteDimensional ℚ E0 := inferInstance
  letI : IsGalois ℚ E0 := IsGalois.of_fixedField_normal_subgroup H0
  refine ⟨E0, inferInstance, inferInstance, inferInstance, K, L, ?_⟩
  constructor
  · infer_instance
  constructor
  · exact IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv hF1)
  constructor
  · exact IsGalois.of_algEquiv (IntermediateField.restrict_algEquiv hF2)
  constructor
  · exact (IntermediateField.restrict_algEquiv hF1).toLinearEquiv.finrank_eq.symm.trans hfinF1
  constructor
  · exact (IntermediateField.restrict_algEquiv hF2).toLinearEquiv.finrank_eq.symm.trans hfinF2
  constructor
  · apply IntermediateField.lift_injective E0
    dsimp only [K, L]
    calc
      IntermediateField.lift (IntermediateField.restrict hF1 ⊓
          IntermediateField.restrict hF2) =
          IntermediateField.lift (IntermediateField.restrict hF1) ⊓
            IntermediateField.lift (IntermediateField.restrict hF2) :=
        IntermediateField.lift_inf ℚ E0 _ _
      _ = F1 ⊓ F2 := by rw [IntermediateField.lift_restrict, IntermediateField.lift_restrict]
      _ = IntermediateField.lift (⊥ : IntermediateField ℚ E0) := by
        rw [show IntermediateField.lift (⊥ : IntermediateField ℚ E0) =
          (⊥ : IntermediateField ℚ C) from IntermediateField.lift_bot ℚ E0]
        apply (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := C)).injective
        dsimp only [F1, F2]
        rw [(IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := C)).map_inf]
        simp only [IntermediateField.fixingSubgroup_fixedField,
          IsGalois.intermediateFieldEquivSubgroup_apply,
          IntermediateField.fixingSubgroup_bot]
        change H1 ⊔ H2 = ⊤
        change eG.comapSubgroup P1 ⊔ eG.comapSubgroup P2 = ⊤
        rw [← eG.comapSubgroup.map_sup, apm_b01A04_cyclotomic_subgroup_sup,
          eG.comapSubgroup.map_top]
  · apply IntermediateField.lift_injective E0
    dsimp only [K, L]
    calc
      IntermediateField.lift (IntermediateField.restrict hF1 ⊔
          IntermediateField.restrict hF2) =
          IntermediateField.lift (IntermediateField.restrict hF1) ⊔
            IntermediateField.lift (IntermediateField.restrict hF2) :=
        IntermediateField.lift_sup ℚ E0 _ _
      _ = F1 ⊔ F2 := by rw [IntermediateField.lift_restrict, IntermediateField.lift_restrict]
      _ = IntermediateField.lift (⊤ : IntermediateField ℚ E0) := by
        rw [show IntermediateField.lift (⊤ : IntermediateField ℚ E0) = E0 from
          IntermediateField.lift_top ℚ E0]
        apply (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := C)).injective
        dsimp only [F1, F2, E0]
        rw [(IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := C)).map_sup]
        simp only [IntermediateField.fixingSubgroup_fixedField,
          IsGalois.intermediateFieldEquivSubgroup_apply]
        change H1 ⊓ H2 = H0
        change eG.comapSubgroup P1 ⊓ eG.comapSubgroup P2 = eG.comapSubgroup P0
        rw [← eG.comapSubgroup.map_inf, apm_b01A04_cyclotomic_subgroup_inf]

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
