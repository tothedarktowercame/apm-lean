import Mathlib

set_option maxHeartbeats 5000000

/-!
# APM b96J04: Splitting fields of `X⁸ + 1`

## Statement repairs

None.

## Encoding questions

None. Both splitting fields are arbitrary field extensions satisfying
`Polynomial.IsSplittingField`. Degree-four subfields are counted as actual
intermediate fields, not replaced by their corresponding subgroups. The
`Fact (Nat.Prime 41)` parameter supplies Mathlib's field structure on `ZMod 41`.
-/

open Polynomial

noncomputable section

local instance apm_b96J04_fact_prime_41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩

def apm_b96J04_fQ : ℚ[X] := X ^ 8 + 1

def apm_b96J04_f41 : (ZMod 41)[X] := X ^ 8 + 1

/-- `X⁸+1` is exactly the sixteenth cyclotomic polynomial over any field. -/
lemma apm_b96J04_X_pow_eight_add_one_eq_cyclotomic
    (F : Type*) [Field F] :
    (X ^ 8 + 1 : F[X]) = cyclotomic 16 F := by
  rw [show (16 : ℕ) = 2 ^ (3 + 1) by norm_num,
    cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  norm_num [Finset.sum_range_succ]
  ring

lemma apm_b96J04_fQ_eq_cyclotomic :
    apm_b96J04_fQ = cyclotomic 16 ℚ := by
  exact apm_b96J04_X_pow_eight_add_one_eq_cyclotomic ℚ

lemma apm_b96J04_f41_eq_cyclotomic :
    apm_b96J04_f41 = cyclotomic 16 (ZMod 41) := by
  exact apm_b96J04_X_pow_eight_add_one_eq_cyclotomic (ZMod 41)

/-- The Frobenius exponent `41` has order two modulo `16`. -/
lemma apm_b96J04_orderOf_41_mod_16 :
    orderOf (41 : ZMod 16) = 2 := by
  apply orderOf_eq_prime
  · decide
  · decide

/-- Every irreducible factor of the finite-field cyclotomic polynomial has
degree two, by the finite-field cyclotomic factorization theorem and the
computed Frobenius order. -/
lemma apm_b96J04_f41_irreducible_factor_degree
    (P : (ZMod 41)[X]) (hP : P ∣ apm_b96J04_f41)
    (hi : Irreducible P) : P.natDegree = 2 := by
  rw [apm_b96J04_f41_eq_cyclotomic] at hP
  rw [Polynomial.natDegree_of_dvd_cyclotomic_of_irreducible
    (p := 41) (f := 1) (by norm_num) (by norm_num) hP hi]
  apply orderOf_eq_prime
  · decide
  · decide

/-- The Frobenius squared fixes every root of `X⁸+1` in its splitting field. -/
lemma apm_b96J04_frobenius_sq_eq_one
    (L : Type*) [Field L] [Algebra (ZMod 41) L]
    [FiniteDimensional (ZMod 41) L] [Finite L]
    [Polynomial.IsSplittingField (ZMod 41) L apm_b96J04_f41] :
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 41) L) ^ 2 = 1 := by
  apply AlgEquiv.ext
  intro x
  have hxmem : x ∈ Algebra.adjoin (ZMod 41) (apm_b96J04_f41.rootSet L) := by
    rw [Polynomial.IsSplittingField.adjoin_rootSet L apm_b96J04_f41]
    exact Set.mem_univ x
  apply Algebra.adjoin_induction (p := fun y _ =>
      ((FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 41) L) ^ 2) y = y)
      (s := apm_b96J04_f41.rootSet L) _ _ _ _ hxmem
  · intro y hy
    have hyroot := (mem_rootSet'.mp hy).2
    have hy8 : y ^ 8 = -1 := by
      have hy0 : y ^ 8 + 1 = 0 := by
        simpa [apm_b96J04_f41, aeval_def] using hyroot
      linear_combination hy0
    have hy16 : y ^ 16 = 1 := by
      rw [show 16 = 8 * 2 by norm_num, pow_mul, hy8]
      ring
    rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    norm_num [Function.iterate_succ_apply, ← pow_mul]
    rw [show 1681 = 16 * 105 + 1 by norm_num, pow_add, pow_mul, hy16]
    simp
  · intro r
    simp
  · intro a b _ _ ha hb
    simpa using congrArg₂ (· + ·) ha hb
  · intro a b _ _ ha hb
    simpa using congrArg₂ (· * ·) ha hb

/-- The Frobenius is nontrivial because it acts by the forty-first power on a
primitive sixteenth root. -/
lemma apm_b96J04_frobenius_ne_one
    (L : Type*) [Field L] [Algebra (ZMod 41) L]
    [FiniteDimensional (ZMod 41) L] [Finite L]
    [Polynomial.IsSplittingField (ZMod 41) L apm_b96J04_f41] :
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 41) L ≠ 1 := by
  obtain ⟨y, hy⟩ := (Polynomial.IsSplittingField.splits L
    apm_b96J04_f41).exists_eval_eq_zero (by
      simp [apm_b96J04_f41, Polynomial.degree_add_eq_left_of_degree_lt])
  letI : CharP L 41 := charP_of_injective_algebraMap' (ZMod 41) 41
  letI : NeZero (16 : L) := ⟨by
    intro h
    have hd : 41 ∣ 16 := (CharP.cast_eq_zero_iff L 41 16).mp h
    norm_num at hd⟩
  have hprim : IsPrimitiveRoot y 16 := by
    rw [← isRoot_cyclotomic_iff, IsRoot.def]
    rw [apm_b96J04_f41_eq_cyclotomic] at hy
    simpa only [map_cyclotomic] using hy
  intro h
  have happ := DFunLike.congr_fun h y
  simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ZMod.card, AlgEquiv.one_apply] at happ
  have hmod : 41 ≡ 1 [MOD 16] := by
    have hm := (hprim.isOfFinOrder (by norm_num)).pow_eq_pow_iff_modEq.mp
      (show y ^ 41 = y ^ 1 by simpa using happ)
    exact hprim.eq_orderOf ▸ hm
  norm_num [Nat.ModEq] at hmod

/-- The finite splitting field has degree two. -/
lemma apm_b96J04_finite_splittingField_finrank
    (L : Type*) [Field L] [Algebra (ZMod 41) L]
    [Polynomial.IsSplittingField (ZMod 41) L apm_b96J04_f41] :
    Module.finrank (ZMod 41) L = 2 := by
  letI : FiniteDimensional (ZMod 41) L :=
    Polynomial.IsSplittingField.finiteDimensional L apm_b96J04_f41
  letI : Finite L := Module.finite_of_finite (ZMod 41)
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  exact orderOf_eq_prime (apm_b96J04_frobenius_sq_eq_one L)
    (apm_b96J04_frobenius_ne_one L)

/-- A cyclic group of cardinality two has the requested concrete
`Multiplicative (ZMod 2)` presentation. -/
lemma apm_b96J04_cyclic_card_two_equiv
    (G : Type*) [Group G] [IsCyclic G] (hcard : Nat.card G = 2) :
    Nonempty (G ≃* Multiplicative (ZMod 2)) := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  exact ⟨(zmodMulEquivOfGenerator hg hcard).symm⟩

/-- The finite-field automorphism group is cyclic of order two. -/
lemma apm_b96J04_finite_aut_equiv
    (L : Type*) [Field L] [Algebra (ZMod 41) L]
    [Polynomial.IsSplittingField (ZMod 41) L apm_b96J04_f41] :
    Nonempty ((L ≃ₐ[ZMod 41] L) ≃* Multiplicative (ZMod 2)) := by
  letI : FiniteDimensional (ZMod 41) L :=
    Polynomial.IsSplittingField.finiteDimensional L apm_b96J04_f41
  letI : Finite L := Module.finite_of_finite (ZMod 41)
  letI : IsGalois (ZMod 41) L := inferInstance
  letI : IsCyclic (L ≃ₐ[ZMod 41] L) := inferInstance
  apply apm_b96J04_cyclic_card_two_equiv
  rw [IsGalois.card_aut_eq_finrank,
    apm_b96J04_finite_splittingField_finrank L]

/-- The concrete unit group modulo `16` has eight elements. -/
lemma apm_b96J04_card_units_mod_16 : Nat.card (ZMod 16)ˣ = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

def apm_b96J04_unitsCode (u : (ZMod 16)ˣ) :
    Multiplicative (ZMod 2 × ZMod 4) :=
  Multiplicative.ofAdd <| match u.1.val with
    | 1  => (0, 0)
    | 3  => (0, 1)
    | 9  => (0, 2)
    | 11 => (0, 3)
    | 15 => (1, 0)
    | 13 => (1, 1)
    | 7  => (1, 2)
    | 5  => (1, 3)
    | _  => (0, 0)

def apm_b96J04_unitsCodeHom :
    (ZMod 16)ˣ →* Multiplicative (ZMod 2 × ZMod 4) where
  toFun := apm_b96J04_unitsCode
  map_one' := by decide
  map_mul' := by decide

lemma apm_b96J04_units_mod_16_equiv :
    Nonempty ((ZMod 16)ˣ ≃* Multiplicative (ZMod 2 × ZMod 4)) := by
  exact ⟨MulEquiv.ofBijective apm_b96J04_unitsCodeHom (by decide)⟩

abbrev apm_b96J04_productGroup := Multiplicative (ZMod 2 × ZMod 4)

def apm_b96J04_pickNontrivial
    (H : {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2}) :
    apm_b96J04_productGroup :=
  (Classical.choose ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2) : H.1)

lemma apm_b96J04_pickNontrivial_spec
    (H : {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2}) :
    apm_b96J04_pickNontrivial H ≠ 1 ∧ apm_b96J04_pickNontrivial H ^ 2 = 1 := by
  let y := Classical.choose ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2)
  have hy := Classical.choose_spec ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2)
  constructor
  · exact fun h => hy.1 (Subtype.ext h)
  · have hp : (y : H.1) ^ 2 = 1 := by
      simpa only [H.2] using (pow_card_eq_one' (x := y))
    exact congrArg Subtype.val hp

def apm_b96J04_orderTwoSubgroupToInvolution
    (H : {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2}) :
    {x : apm_b96J04_productGroup // x ≠ 1 ∧ x ^ 2 = 1} :=
  ⟨apm_b96J04_pickNontrivial H, apm_b96J04_pickNontrivial_spec H⟩

lemma apm_b96J04_zpowers_card_two
    (x : {x : apm_b96J04_productGroup // x ≠ 1 ∧ x ^ 2 = 1}) :
    Nat.card (Subgroup.zpowers x.1) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime x.2.2 x.2.1

def apm_b96J04_involutionToOrderTwoSubgroup
    (x : {x : apm_b96J04_productGroup // x ≠ 1 ∧ x ^ 2 = 1}) :
    {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2} :=
  ⟨Subgroup.zpowers x.1, apm_b96J04_zpowers_card_two x⟩

lemma apm_b96J04_orderTwoSubgroup_roundtrip
    (H : {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2}) :
    apm_b96J04_involutionToOrderTwoSubgroup
      (apm_b96J04_orderTwoSubgroupToInvolution H) = H := by
  apply Subtype.ext
  change Subgroup.zpowers (apm_b96J04_pickNontrivial H) = H.1
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    exact (Classical.choose ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2)).property
  · intro z hz
    by_cases he : z = 1
    · subst z
      exact Subgroup.one_mem _
    · have hu :=
        (Classical.choose_spec ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2)).2
      have heq : (⟨z, hz⟩ : H.1) =
          Classical.choose ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2) :=
        hu _ (fun h => he (congrArg Subtype.val h))
      rw [show z = apm_b96J04_pickNontrivial H by exact congrArg Subtype.val heq]
      exact Subgroup.mem_zpowers _

lemma apm_b96J04_involution_roundtrip
    (x : {x : apm_b96J04_productGroup // x ≠ 1 ∧ x ^ 2 = 1}) :
    apm_b96J04_orderTwoSubgroupToInvolution
      (apm_b96J04_involutionToOrderTwoSubgroup x) = x := by
  apply Subtype.ext
  change apm_b96J04_pickNontrivial
    (apm_b96J04_involutionToOrderTwoSubgroup x) = x.1
  let H := apm_b96J04_involutionToOrderTwoSubgroup x
  have hu := (Classical.choose_spec ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2)).2
  have hxmem : x.1 ∈ H.1 := Subgroup.mem_zpowers x.1
  have heq : (⟨x.1, hxmem⟩ : H.1) =
      Classical.choose ((Nat.card_eq_two_iff' (1 : H.1)).mp H.2) :=
    hu _ (fun h => x.2.1 (congrArg Subtype.val h))
  exact (congrArg Subtype.val heq).symm

def apm_b96J04_orderTwoSubgroupsEquivInvolutions :
    {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2} ≃
      {x : apm_b96J04_productGroup // x ≠ 1 ∧ x ^ 2 = 1} where
  toFun := apm_b96J04_orderTwoSubgroupToInvolution
  invFun := apm_b96J04_involutionToOrderTwoSubgroup
  left_inv := apm_b96J04_orderTwoSubgroup_roundtrip
  right_inv := apm_b96J04_involution_roundtrip

lemma apm_b96J04_card_orderTwoSubgroups :
    Nat.card {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2} = 3 := by
  rw [Nat.card_congr apm_b96J04_orderTwoSubgroupsEquivInvolutions,
    Nat.card_eq_fintype_card]
  decide

/-- The Galois correspondence and an automorphism-group equivalence identify
degree-four intermediate fields in a degree-eight extension with order-two
subgroups of the concrete product group. -/
lemma apm_b96J04_card_transport_fixingSubgroup
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (eG : (K ≃ₐ[ℚ] K) ≃* apm_b96J04_productGroup)
    (E : IntermediateField ℚ K) :
    Nat.card (eG.symm.comapSubgroup E.fixingSubgroup) = Module.finrank E K := by
  rw [show eG.symm.comapSubgroup E.fixingSubgroup =
      Subgroup.map eG.toMonoidHom E.fixingSubgroup by
    exact Subgroup.comap_equiv_eq_map_symm eG.symm E.fixingSubgroup]
  rw [← IsGalois.card_fixingSubgroup_eq_finrank E]
  exact (Nat.card_congr (eG.subgroupMap E.fixingSubgroup).toEquiv).symm

def apm_b96J04_degreeFourFieldsEquivOrderTwoSubgroups
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (eG : (K ≃ₐ[ℚ] K) ≃* apm_b96J04_productGroup)
    (htotal : Module.finrank ℚ K = 8) :
    {E : IntermediateField ℚ K // Module.finrank ℚ E = 4} ≃
      {H : Subgroup apm_b96J04_productGroup // Nat.card H = 2} := by
  let e : IntermediateField ℚ K ≃ Subgroup apm_b96J04_productGroup :=
    (IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := K)).toEquiv.trans
      eG.symm.comapSubgroup.toEquiv
  apply Equiv.subtypeEquiv e
  intro E
  change Module.finrank ℚ E = 4 ↔ Nat.card (e E) = 2
  have hcard : Nat.card (e E) = Module.finrank E K :=
    apm_b96J04_card_transport_fixingSubgroup K eG E
  rw [hcard]
  have ht := Module.finrank_mul_finrank ℚ E K
  rw [htotal] at ht
  constructor
  · intro h
    rw [h] at ht
    omega
  · intro h
    rw [h] at ht
    omega

lemma apm_b96J04_isCyclotomicExtension_of_isSplittingField
    (K : Type*) [Field K] [Algebra ℚ K]
    [Polynomial.IsSplittingField ℚ K (cyclotomic 16 ℚ)] :
    IsCyclotomicExtension {16} ℚ K := by
  letI : CharZero K :=
    charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  letI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  letI : NeZero (16 : K) := ⟨Nat.cast_ne_zero.mpr (by norm_num)⟩
  rw [IsCyclotomicExtension.iff_singleton]
  obtain ⟨ζ, hζ⟩ := (Polynomial.IsSplittingField.splits K
    (cyclotomic 16 ℚ)).exists_eval_eq_zero
      (by simpa only [map_cyclotomic] using
        (degree_cyclotomic_pos 16 K (by norm_num)).ne')
  have hprim : IsPrimitiveRoot ζ 16 := by
    rw [← isRoot_cyclotomic_iff, IsRoot.def]
    simpa only [map_cyclotomic] using hζ
  refine ⟨⟨ζ, hprim⟩, ?_⟩
  have htop : Algebra.adjoin ℚ {b : K | b ^ 16 = 1} = ⊤ := by
    have heq :=
      IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots
        (A := ℚ) hprim
    simp only [Set.mem_singleton_iff, exists_eq_left, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, true_and] at heq
    rw [← heq]
    exact Polynomial.IsSplittingField.adjoin_rootSet K (cyclotomic 16 ℚ)
  exact Algebra.eq_top_iff.mp htop

/-- Once the abstract splitting field has been recognized as the sixteenth
cyclotomic extension, Mathlib's rational cyclotomic Galois equivalence applies
directly.  This packages both the automorphism-group model and its cardinality,
isolating recognition of the splitting field as the sole upstream bridge. -/
lemma apm_b96J04_aut_equiv_units_of_isCyclotomic
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {16} ℚ K] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* (ZMod 16)ˣ) ∧
      Nat.card (K ≃ₐ[ℚ] K) = 8 := by
  let e := IsCyclotomicExtension.Rat.galEquivZMod 16 K
  refine ⟨⟨e⟩, ?_⟩
  rw [Nat.card_congr e.toEquiv, apm_b96J04_card_units_mod_16]

/-- The concrete unit-group equivalence completes the rational automorphism
group identification once the splitting field has been recognized as the
sixteenth cyclotomic extension. -/
lemma apm_b96J04_aut_equiv_product_of_isCyclotomic
    (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {16} ℚ K] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2 × ZMod 4)) := by
  obtain ⟨eunits⟩ := apm_b96J04_units_mod_16_equiv
  exact ⟨(IsCyclotomicExtension.Rat.galEquivZMod 16 K).trans eunits⟩

/-- Changing the (necessarily unique) rational algebra structure does not
change the automorphism group.  Keeping this transport explicit avoids an
instance-coherence gap between a caller-supplied algebra and the canonical
algebra installed by `NumberField`. -/
def apm_b96J04_ratAutChange (K : Type*) [Field K]
    (A B : Algebra ℚ K) :
    (@AlgEquiv ℚ K K _ _ _ A A) ≃* (@AlgEquiv ℚ K K _ _ _ B B) where
  toFun σ :=
    @AlgEquiv.ofRingEquiv ℚ K K _ _ _ B B
      (@AlgEquiv.toRingEquiv ℚ K K _ _ _ A A σ) (fun x => by
        rw [show (@algebraMap ℚ K _ _ B) x = (@algebraMap ℚ K _ _ A) x by
          exact DFunLike.congr_fun (Subsingleton.elim _ _) x]
        exact @AlgEquiv.commutes ℚ K K _ _ _ A A σ x)
  invFun σ :=
    @AlgEquiv.ofRingEquiv ℚ K K _ _ _ A A
      (@AlgEquiv.toRingEquiv ℚ K K _ _ _ B B σ) (fun x => by
        rw [show (@algebraMap ℚ K _ _ A) x = (@algebraMap ℚ K _ _ B) x by
          exact DFunLike.congr_fun (Subsingleton.elim _ _) x]
        exact @AlgEquiv.commutes ℚ K K _ _ _ B B σ x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The rational automorphism-group conclusion, including transport from the
arbitrary algebra structure in the frozen statement. -/
lemma apm_b96J04_aut_equiv_product_of_isSplittingField
    (K : Type*) [Field K] [Algebra ℚ K]
    [Polynomial.IsSplittingField ℚ K apm_b96J04_fQ] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2 × ZMod 4)) := by
  rw [apm_b96J04_fQ_eq_cyclotomic] at *
  let hA : Algebra ℚ K := inferInstance
  letI hcyc : IsCyclotomicExtension {16} ℚ K :=
    apm_b96J04_isCyclotomicExtension_of_isSplittingField K
  letI hnum : NumberField K := IsCyclotomicExtension.numberField {16} ℚ K
  let hCan : Algebra ℚ K := DivisionRing.toRatAlgebra
  have hEq : hA = hCan := Subsingleton.elim _ _
  let hcycCan : @IsCyclotomicExtension {16} ℚ K _ _ hCan := hEq ▸ hcyc
  let eCan := @IsCyclotomicExtension.Rat.galEquivZMod 16 inferInstance K
    inferInstance hnum hcycCan
  obtain ⟨eunits⟩ := apm_b96J04_units_mod_16_equiv
  exact ⟨(apm_b96J04_ratAutChange K hA hCan).trans (eCan.trans eunits)⟩

/-- An arbitrary rational splitting field in the frozen statement is a finite
Galois extension of degree eight.  This is the common prerequisite for the
Galois-correspondence counts. -/
lemma apm_b96J04_rational_splittingField_galois_finrank
    (K : Type*) [Field K] [Algebra ℚ K]
    [Polynomial.IsSplittingField ℚ K apm_b96J04_fQ] :
    IsGalois ℚ K ∧ Module.finrank ℚ K = 8 := by
  rw [apm_b96J04_fQ_eq_cyclotomic] at *
  letI : IsCyclotomicExtension {16} ℚ K :=
    apm_b96J04_isCyclotomicExtension_of_isSplittingField K
  letI : FiniteDimensional ℚ K := IsCyclotomicExtension.finite {16} ℚ K
  constructor
  · exact IsCyclotomicExtension.isGalois {16} ℚ K
  · rw [IsCyclotomicExtension.finrank (n := 16) K
      (Polynomial.cyclotomic.irreducible_rat (by norm_num))]
    decide

/-- Both rational intermediate-field counts follow from the explicit
order-two subgroup enumeration. -/
lemma apm_b96J04_rational_intermediateField_count
    (K : Type*) [Field K] [Algebra ℚ K]
    [Polynomial.IsSplittingField ℚ K apm_b96J04_fQ] :
    Nat.card {E : IntermediateField ℚ K // Module.finrank ℚ E = 4} = 3 := by
  letI : FiniteDimensional ℚ K :=
    Polynomial.IsSplittingField.finiteDimensional K apm_b96J04_fQ
  obtain ⟨hg, hfin⟩ := apm_b96J04_rational_splittingField_galois_finrank K
  letI : IsGalois ℚ K := hg
  obtain ⟨eG⟩ := apm_b96J04_aut_equiv_product_of_isSplittingField K
  rw [Nat.card_congr
    (apm_b96J04_degreeFourFieldsEquivOrderTwoSubgroups K eG hfin),
    apm_b96J04_card_orderTwoSubgroups]

/-- In a rational Galois extension with commutative automorphism group, every
intermediate field is Galois over `ℚ`.  The final step explicitly transports
from the inherited intermediate-field algebra to Mathlib's canonical rational
algebra, which is the instance used by the frozen predicate. -/
lemma apm_b96J04_intermediate_isGalois_of_commAut
    (K : Type*) [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    [IsGalois ℚ K]
    (eG : (K ≃ₐ[ℚ] K) ≃* apm_b96J04_productGroup)
    (E : IntermediateField ℚ K) : IsGalois ℚ E := by
  have hcomm (x y : K ≃ₐ[ℚ] K) : x * y = y * x := by
    apply eG.injective
    simp only [map_mul]
    exact mul_comm _ _
  let A : Algebra ℚ E := E.algebra'
  let hg : @IsGalois ℚ _ E _ A := by
    letI : Algebra ℚ E := A
    have hn : E.fixingSubgroup.Normal := ⟨fun n hn g => by
      rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]
      exact hn⟩
    exact (InfiniteGalois.normal_iff_isGalois E).mp hn
  let B : Algebra ℚ E := DivisionRing.toRatAlgebra
  letI : Algebra ℚ E := B
  letI : @IsGalois ℚ _ E _ A := hg
  apply @IsGalois.of_equiv_equiv (F := ℚ) (E := E) (M := ℚ) (N := E)
    _ _ A _ _ B inferInstance hg (RingEquiv.refl ℚ) (RingEquiv.refl E)
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (Subsingleton.elim
    (@algebraMap ℚ E _ _ B) (@algebraMap ℚ E _ _ A)) x

/-- All three degree-four rational intermediate fields are Galois. -/
lemma apm_b96J04_rational_galois_intermediateField_count
    (K : Type*) [Field K] [Algebra ℚ K]
    [Polynomial.IsSplittingField ℚ K apm_b96J04_fQ] :
    Nat.card {E : IntermediateField ℚ K //
      Module.finrank ℚ E = 4 ∧ IsGalois ℚ E} = 3 := by
  letI : FiniteDimensional ℚ K :=
    Polynomial.IsSplittingField.finiteDimensional K apm_b96J04_fQ
  obtain ⟨hg, _⟩ := apm_b96J04_rational_splittingField_galois_finrank K
  letI : IsGalois ℚ K := hg
  obtain ⟨eG⟩ := apm_b96J04_aut_equiv_product_of_isSplittingField K
  let efilter :
      {E : IntermediateField ℚ K // Module.finrank ℚ E = 4 ∧ IsGalois ℚ E} ≃
        {E : IntermediateField ℚ K // Module.finrank ℚ E = 4} := {
    toFun E := ⟨E.1, E.2.1⟩
    invFun E := ⟨E.1, E.2, apm_b96J04_intermediate_isGalois_of_commAut K eG E.1⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr efilter, apm_b96J04_rational_intermediateField_count K]

theorem apm_b96j04
    (K L : Type) [Field K] [Algebra ℚ K]
    [Fact (Nat.Prime 41)] [Field L] [Algebra (ZMod 41) L]
    [apm_b96J04_fQ.IsSplittingField ℚ K]
    [apm_b96J04_f41.IsSplittingField (ZMod 41) L] :
    Nonempty
      ((K ≃ₐ[ℚ] K) ≃* Multiplicative (ZMod 2 × ZMod 4)) ∧
    Nat.card
      {E : IntermediateField ℚ K // Module.finrank ℚ E = 4} = 3 ∧
    Nat.card
      {E : IntermediateField ℚ K //
        Module.finrank ℚ E = 4 ∧ IsGalois ℚ E} = 3 ∧
    Nonempty
      ((L ≃ₐ[ZMod 41] L) ≃* Multiplicative (ZMod 2)) := by
  /-
  PARTIAL boundary (closer hop 2): the polynomial identification is now
  compiled uniformly over every field as
  `apm_b96J04_X_pow_eight_add_one_eq_cyclotomic`, with specialized rewrite
  lemmas for both frozen base fields. Thus both arbitrary splitting-field
  instances can be rewritten literally as splitting fields of `cyclotomic 16`.

  Closer hop 2 compiles the concrete arithmetic on both sides of the missing
  transport. `apm_b96J04_orderOf_41_mod_16` proves that the Frobenius exponent
  has order exactly two, using `orderOf_eq_prime` and decidable arithmetic in
  `ZMod 16`. `apm_b96J04_card_units_mod_16` proves that `(ZMod 16)ˣ` has eight
  elements. A direct computational search cannot synthesize the requested
  structured group equivalence, and Mathlib's cyclotomic searches expose
  `IsCyclotomicExtension.finrank` over irreducible cyclotomic polynomials but
  no finite-field splitting-degree theorem consuming this order computation.

  The informal proof then uses the cyclotomic Galois-group
  isomorphism over `ℚ` and the Frobenius-order description over `ZMod 41`.
  Searches covered `Polynomial.IsSplittingField`,
  `FieldTheory.Galois.IsGaloisGroup`, `IntermediateField.finrank_fixedField_eq_card`,
  and Mathlib's cyclotomic files. The general Galois correspondence is present,
  but no compiled bridge was found that identifies `(K ≃ₐ[ℚ] K)` for this
  arbitrary splitting-field instance with `(ZMod 16)ˣ`, or identifies the
  finite-field splitting degree with the now-compiled value of
  `orderOf (41 : ZMod 16)`. Without those
  identifications, neither the automorphism-group conclusions nor the exact
  count of degree-four intermediate fields can be reached. No proof step
  compiled within the skip budget.

  CLOSER HOP 3: `apm_b96J04_aut_equiv_units_of_isCyclotomic` now compiles the
  rational Galois transport after the precise missing recognition hypothesis.
  Given `IsCyclotomicExtension {16} ℚ K`, it applies
  `IsCyclotomicExtension.Rat.galEquivZMod` and obtains both the group
  equivalence `(K ≃ₐ[ℚ] K) ≃* (ZMod 16)ˣ` and cardinality eight, reusing the
  hop-2 unit-cardinality computation. Thus no further arbitrary-splitting-
  field transport is required after constructing that cyclotomic-extension
  instance.

  Searches beyond hop 2 covered the definition and singleton criteria for
  `IsCyclotomicExtension`, primitive-root/cyclotomic-root lemmas, rational
  `galEquivZMod`, and finite abelian group classification. They found no
  packaged conversion from `IsSplittingField ℚ K (cyclotomic 16 ℚ)` to the
  required cyclotomic-extension instance, nor a packaged structured
  equivalence `(ZMod 16)ˣ ≃* Multiplicative (ZMod 2 × ZMod 4)`. The finite-
  field Frobenius-degree bridge and subsequent subgroup enumeration also
  remain open.
  -/
  /-
  HOP 4 closes both identified rational-side holes.  The explicit computable
  homomorphism `apm_b96J04_unitsCodeHom` yields the requested structured unit
  equivalence, while
  `apm_b96J04_isCyclotomicExtension_of_isSplittingField` converts the literal
  cyclotomic splitting-field instance by comparing its root-set adjoin with
  the primitive-root adjoin characterization.  Their composite proves the
  rational automorphism-group conclusion in
  `apm_b96J04_aut_equiv_product_of_isCyclotomic`.  Applying that conclusion
  inside the frozen theorem still encounters its explicitly supplied
  rational `Algebra` instance versus `NumberField`'s canonical rational
  algebra, while the independent intermediate-field counts and finite-field
  Frobenius automorphism clause also remain open.

  HOP 5 installs the cyclotomic structure on the arbitrary rational splitting
  field and proves in `apm_b96J04_rational_splittingField_galois_finrank` that
  it is Galois of absolute degree eight.  This removes the degree calculation
  from the intermediate-field enumeration: under the finite Galois
  correspondence, the requested degree-four fields correspond exactly to
  order-two subgroups of the eight-element automorphism group.  Experiments
  also isolated an instance-coherence obstruction in applying the existing
  rational `galEquivZMod`: `NumberField K` activates Mathlib's canonical
  rational algebra, while the frozen theorem quantifies an arbitrary
  propositionally equal `Algebra ℚ K`.

  HOP 6 closes that instance-coherence obstruction.  The explicit
  `apm_b96J04_ratAutChange` transports automorphisms between any two rational
  algebra structures on the same field without dependent instance
  elimination.  `apm_b96J04_aut_equiv_product_of_isSplittingField` composes
  this with `galEquivZMod` and the concrete unit equivalence, proving the first
  conjunct of the frozen theorem for its caller-supplied algebra.  The
  remaining rational work is exactly the enumeration of the three order-two
  subgroups (normality is automatic in the abelian product).  Independently,
  the finite-field conclusion still needs the Frobenius/order-to-degree bridge.

  HOP 7 applies Mathlib's finite-field cyclotomic factorization theorem at the
  exact frozen parameters.  `apm_b96J04_f41_irreducible_factor_degree` proves
  that every irreducible factor of `X^8+1` over `ZMod 41` has degree two.  The
  remaining finite-field step is consequently narrowed to the standard lemma
  that the splitting field of a squarefree polynomial whose irreducible
  factors all have degree two has degree two; after that, finite-field Galois
  cyclicity supplies the requested two-element automorphism group.

  HOP 8 closes the finite group enumeration underlying both rational counts.
  `apm_b96J04_orderTwoSubgroupsEquivInvolutions` proves, without relying on a
  noncomputable subgroup enumeration, that order-two subgroups of
  `Multiplicative (ZMod 2 × ZMod 4)` are equivalent to its nonidentity
  involutions.  The latter subtype is computable, and
  `apm_b96J04_card_orderTwoSubgroups` establishes that its cardinality is
  exactly three.  What remains on the rational side is only transport of this
  cardinality through the automorphism-group equivalence and the finite
  Galois correspondence, plus the normality/`IsGalois` predicate transport.

  HOP 9 performs the cardinality transport itself.  The compiled equivalence
  `apm_b96J04_degreeFourFieldsEquivOrderTwoSubgroups` composes the finite
  Galois correspondence with subgroup transport along the concrete
  automorphism equivalence; the tower finrank identity converts absolute
  degree four into subgroup order two.  Consequently
  `apm_b96J04_rational_intermediateField_count` proves the second conjunct of
  the frozen theorem.  The only rational residual is now the Galois-filtered
  version, i.e. transporting normality across the caller-supplied rational
  algebra structure.

  HOP 10 closes that last rational residual.  Commutativity is pulled back
  pointwise through the automorphism equivalence without replacing Lean's
  existing group instance; every fixing subgroup is therefore normal.
  `apm_b96J04_intermediate_isGalois_of_commAut` then transports the resulting
  Galois witness from the inherited intermediate-field algebra to the
  canonical rational algebra.  The filtered subtype is equivalent to the
  unfiltered one, so `apm_b96J04_rational_galois_intermediateField_count`
  proves the third conjunct.  Only the independent finite-field automorphism
  clause remains.

  HOP 11 closes the finite-field clause and the theorem.  Frobenius squared
  fixes every root because each satisfies `y^16 = 1` and `41^2 ≡ 1 mod 16`;
  the splitting-field adjoin property extends this equality to all of `L`.
  Frobenius itself is nontrivial on a primitive sixteenth root, so its order,
  hence the extension finrank, is exactly two.  Finite-field Galois cyclicity
  and `zmodMulEquivOfGenerator` then identify the automorphism group with
  `Multiplicative (ZMod 2)`.
  -/
  refine ⟨apm_b96J04_aut_equiv_product_of_isSplittingField K,
    apm_b96J04_rational_intermediateField_count K,
    apm_b96J04_rational_galois_intermediateField_count K, ?_⟩
  exact apm_b96J04_finite_aut_equiv L
