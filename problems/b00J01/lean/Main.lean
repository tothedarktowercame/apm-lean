import Mathlib

/-!
# APM b00J01

## Statement repairs

None.

## Encoding questions

None. Splitting fields are quantified abstractly via `IsSplittingField`, so the
answer is independent of the chosen construction. The six intermediate fields
over `ℚ` are described by their degrees, with the three cubic fields identified
exactly as the non-Galois ones.
-/

open Polynomial

/-- The polynomial `X³ - 7` over a field. -/
noncomputable def apm_b00j01_poly (F : Type*) [Field F] : Polynomial F :=
  X ^ 3 - C 7

local instance apm_b00j01_fact_prime_13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The concrete cubic-residue calculation underlying the finite-field part. -/
lemma apm_b00j01_seven_not_cube_mod13 :
    ∀ x : ZMod 13, x ^ 3 ≠ 7 := by
  decide

/-- Consequently `X³ - 7` has no root over `𝔽₁₃`. -/
lemma apm_b00j01_not_isRoot_mod13 (x : ZMod 13) :
    ¬IsRoot (apm_b00j01_poly (ZMod 13)) x := by
  simp only [IsRoot, apm_b00j01_poly, eval_sub, eval_pow, eval_X, eval_C]
  exact sub_ne_zero.mpr (apm_b00j01_seven_not_cube_mod13 x)

/-- The polynomial defining the finite-field splitting field is irreducible. -/
lemma apm_b00j01_irreducible_mod13 :
    Irreducible (apm_b00j01_poly (ZMod 13)) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · norm_num [apm_b00j01_poly]
  · exact apm_b00j01_not_isRoot_mod13

lemma apm_b00j01_separable_mod13 :
    (apm_b00j01_poly (ZMod 13)).Separable :=
  PerfectField.separable_of_irreducible apm_b00j01_irreducible_mod13

/-- `3` is a primitive cube root of unity modulo `13`. -/
lemma apm_b00j01_primitiveRoot_three_mod13 :
    IsPrimitiveRoot (3 : ZMod 13) 3 := by
  have horder : orderOf (3 : ZMod 13) = 3 := by
    apply (orderOf_eq_iff (by norm_num)).2
    constructor
    · decide
    · intro m hm hm0
      interval_cases m <;> decide
  refine ⟨by decide, fun l hl => ?_⟩
  rw [← horder]
  exact orderOf_dvd_of_pow_eq_one hl

lemma apm_b00j01_finiteField_isGalois
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    IsGalois (ZMod 13) M := by
  letI : FiniteDimensional (ZMod 13) M :=
    IsSplittingField.finiteDimensional M (apm_b00j01_poly (ZMod 13))
  exact IsGalois.of_separable_splitting_field apm_b00j01_separable_mod13

lemma apm_b00j01_finiteField_card_aut
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    Nat.card (M ≃ₐ[ZMod 13] M) = Module.finrank (ZMod 13) M := by
  letI : FiniteDimensional (ZMod 13) M :=
    IsSplittingField.finiteDimensional M (apm_b00j01_poly (ZMod 13))
  letI : IsGalois (ZMod 13) M := apm_b00j01_finiteField_isGalois M
  exact IsGalois.card_aut_eq_finrank (ZMod 13) M

/-- Irreducibility already forces the arbitrary splitting field's degree to
be a multiple of three.  This is the exact lower-degree constraint needed
before identifying it with the canonical degree-three Galois field. -/
lemma apm_b00j01_three_dvd_finiteField_finrank
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    3 ∣ Module.finrank (ZMod 13) M := by
  have hdvd := apm_b00j01_irreducible_mod13.natDegree_dvd_finrank
    (Polynomial.IsSplittingField.splits M (apm_b00j01_poly (ZMod 13)))
  norm_num [apm_b00j01_poly] at hdvd ⊢
  exact hdvd

/-- Consequently the automorphism group of the finite-field splitting field
has cardinality divisible by three. -/
lemma apm_b00j01_three_dvd_finiteField_card_aut
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    3 ∣ Nat.card (M ≃ₐ[ZMod 13] M) := by
  rw [apm_b00j01_finiteField_card_aut M]
  exact apm_b00j01_three_dvd_finiteField_finrank M

/-- The two real-algebra automorphisms of `ℂ` are the identity and complex
conjugation. -/
lemma apm_b00j01_complex_aut_eq_one_or_conj (σ : ℂ ≃ₐ[ℝ] ℂ) :
    σ = 1 ∨ σ = Complex.conjAe := by
  rcases Complex.real_algHom_eq_id_or_conj σ.toAlgHom with h | h
  · left
    ext z
    exact DFunLike.congr_fun h z
  · right
    ext z
    exact DFunLike.congr_fun h z

/-- The real-algebra automorphism group of `ℂ` is the cyclic group of order
two.  This isolates the group-theoretic half of the real splitting-field
bridge from the still-needed proof that the concrete cubic splits in `ℂ`. -/
lemma apm_b00j01_complex_aut_mulEquiv_zmod_two :
    Nonempty ((ℂ ≃ₐ[ℝ] ℂ) ≃* Multiplicative (ZMod 2)) := by
  letI : Finite (ℂ ≃ₐ[ℝ] ℂ) := inferInstance
  have hne : (1 : ℂ ≃ₐ[ℝ] ℂ) ≠ Complex.conjAe := by
    intro h
    have hI := DFunLike.congr_fun h Complex.I
    change Complex.I = star Complex.I at hI
    rw [← starRingEnd_apply, Complex.conj_I] at hI
    have him := congrArg Complex.im hI
    norm_num at him
  have hcard : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, Complex.conjAe, hne, ?_⟩
    apply Set.eq_univ_of_forall
    intro σ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    exact apm_b00j01_complex_aut_eq_one_or_conj σ
  have hcyc : IsCyclic (ℂ ≃ₐ[ℝ] ℂ) := by
    letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    exact isCyclic_of_prime_card hcard
  let e := (zmodCyclicMulEquiv hcyc).symm
  rw [hcard] at e
  exact ⟨e⟩

/-- Once `ℂ` is supplied as a concrete splitting field, uniqueness of
splitting fields transports its computed automorphism group to every abstract
real splitting field. -/
lemma apm_b00j01_real_bridge_of_complex_splitting
    (hℂ : IsSplittingField ℝ ℂ (apm_b00j01_poly ℝ))
    (L : Type*) [Field L] [Algebra ℝ L]
    [IsSplittingField ℝ L (apm_b00j01_poly ℝ)] :
    Nonempty ((L ≃ₐ[ℝ] L) ≃* Multiplicative (ZMod 2)) := by
  letI : IsSplittingField ℝ ℂ (apm_b00j01_poly ℝ) := hℂ
  let e : L ≃ₐ[ℝ] ℂ :=
    (Polynomial.IsSplittingField.algEquiv L (apm_b00j01_poly ℝ)).trans
      (Polynomial.IsSplittingField.algEquiv ℂ (apm_b00j01_poly ℝ)).symm
  exact apm_b00j01_complex_aut_mulEquiv_zmod_two.map
    (AlgEquiv.autCongr e).trans

/-- For a real polynomial which splits in `ℂ`, it is enough to show that its
roots generate `I`; the real and imaginary decomposition then shows that they
generate all of `ℂ`. -/
lemma apm_b00j01_complex_isSplittingField_of_I_mem
    (p : Polynomial ℝ)
    (hsplits : (p.map (algebraMap ℝ ℂ)).Splits)
    (hI : Complex.I ∈ Algebra.adjoin ℝ (p.rootSet ℂ)) :
    IsSplittingField ℝ ℂ p := by
  constructor
  · exact hsplits
  · apply top_unique
    intro z _
    have hz := (Algebra.adjoin ℝ (p.rootSet ℂ)).add_mem
      ((Algebra.adjoin ℝ (p.rootSet ℂ)).algebraMap_mem z.re)
      ((Algebra.adjoin ℝ (p.rootSet ℂ)).mul_mem
        ((Algebra.adjoin ℝ (p.rootSet ℂ)).algebraMap_mem z.im) hI)
    simpa using hz

/-- A primitive cube root of unity in `ℂ` is genuinely nonreal.  This is the
key generation fact for recovering `I` from a nonreal root of the cubic. -/
lemma apm_b00j01_primitive_cube_root_im_ne_zero
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ 3) : ζ.im ≠ 0 := by
  intro him
  have hre : ζ.re ^ 3 = 1 := by
    have hp := congrArg Complex.re hζ.pow_eq_one
    simpa [pow_succ, Complex.mul_re, him] using hp
  have hre_one : ζ.re = 1 := by
    apply (show Odd 3 by decide).pow_injective
    simpa using hre
  have hzeta_one : ζ = 1 := by
    apply Complex.ext
    · simpa using hre_one
    · simp [him]
  exact hζ.ne_one (by norm_num) hzeta_one

/-- Any nonreal complex element contained in a real subalgebra generates `I`
inside that subalgebra. -/
lemma apm_b00j01_I_mem_of_nonreal_mem_adjoin
    {S : Set ℂ} {z : ℂ} (hz : z ∈ Algebra.adjoin ℝ S) (him : z.im ≠ 0) :
    Complex.I ∈ Algebra.adjoin ℝ S := by
  have hre : (algebraMap ℝ ℂ z.re) ∈ Algebra.adjoin ℝ S :=
    (Algebra.adjoin ℝ S).algebraMap_mem z.re
  have him_inv : (algebraMap ℝ ℂ z.im⁻¹) ∈ Algebra.adjoin ℝ S :=
    (Algebra.adjoin ℝ S).algebraMap_mem z.im⁻¹
  have hmem := (Algebra.adjoin ℝ S).mul_mem him_inv
    ((Algebra.adjoin ℝ S).sub_mem hz hre)
  convert hmem using 1
  apply Complex.ext <;> simp [him]

/-- The concrete complex splitting field for `X³ - 7` over `ℝ`. -/
lemma apm_b00j01_complex_isSplittingField :
    IsSplittingField ℝ ℂ (apm_b00j01_poly ℝ) := by
  let α : ℝ := (7 : ℝ) ^ ((3 : ℝ)⁻¹)
  let ζ : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)
  have hα : α ^ 3 = 7 := by
    exact Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have hαc : (α : ℂ) ^ 3 = 7 := by exact_mod_cast hα
  have hαpos : 0 < α := Real.rpow_pos_of_pos (by norm_num) _
  have hζ : IsPrimitiveRoot ζ 3 := by
    exact Complex.isPrimitiveRoot_exp 3 (by norm_num)
  apply apm_b00j01_complex_isSplittingField_of_I_mem
  · have hs : (X ^ 3 - C (7 : ℂ)).Splits := by
      apply X_pow_sub_C_splits_of_isPrimitiveRoot
        (ζ := ζ) (α := (α : ℂ)) hζ
      exact hαc
    simpa [apm_b00j01_poly] using hs
  · apply apm_b00j01_I_mem_of_nonreal_mem_adjoin
      (z := ζ * (α : ℂ))
    · apply Algebra.subset_adjoin
      rw [Polynomial.mem_rootSet]
      constructor
      · intro hp
        have hd : (apm_b00j01_poly ℝ).natDegree = 3 := by
          norm_num [apm_b00j01_poly]
        rw [hp] at hd
        simp at hd
      · rw [aeval_def]
        simp [apm_b00j01_poly, mul_pow, hαc, hζ.pow_eq_one]
    · simp [Complex.mul_im, hαpos.ne',
        apm_b00j01_primitive_cube_root_im_ne_zero hζ]

/-- Reduction modulo `13` and Gauss's lemma prove the rational cubic
irreducible without a separate rational-cube denominator argument. -/
lemma apm_b00j01_irreducible_rat : Irreducible (apm_b00j01_poly ℚ) := by
  let f : ℤ[X] := X ^ 3 - C 7
  have hfmonic : f.Monic := by
    exact monic_X_pow_sub_C 7 (by norm_num)
  have hfmod : Irreducible (f.map (Int.castRingHom (ZMod 13))) := by
    simpa [f, apm_b00j01_poly] using apm_b00j01_irreducible_mod13
  have hfi : Irreducible f := Monic.irreducible_of_irreducible_map
    (Int.castRingHom (ZMod 13)) f hfmonic hfmod
  have hfprim : f.IsPrimitive := hfmonic.isPrimitive
  have hfq : Irreducible (f.map (algebraMap ℤ ℚ)) :=
    hfprim.irreducible_iff_irreducible_map_fraction_map.mp hfi
  simpa [f, apm_b00j01_poly] using hfq

/-- The rational cubic has one real root and three complex roots, hence
exactly two nonreal roots in the cardinality form expected by the prime-degree
Galois-action theorem. -/
lemma apm_b00j01_rootSet_card_relation :
    Fintype.card ((apm_b00j01_poly ℚ).rootSet ℂ) =
      Fintype.card ((apm_b00j01_poly ℚ).rootSet ℝ) + 2 := by
  let α : ℝ := (7 : ℝ) ^ ((3 : ℝ)⁻¹)
  have hα : α ^ 3 = 7 :=
    Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have hαroot : α ∈ (apm_b00j01_poly ℚ).rootSet ℝ := by
    rw [Polynomial.mem_rootSet]
    constructor
    · exact apm_b00j01_irreducible_rat.ne_zero
    · rw [aeval_def]
      norm_num [apm_b00j01_poly, hα]
  letI : Unique ((apm_b00j01_poly ℚ).rootSet ℝ) := {
    default := ⟨α, hαroot⟩
    uniq x := by
      apply Subtype.ext
      apply (show Odd 3 by decide).pow_injective
      have hx := (Polynomial.mem_rootSet.mp x.2).2
      have hx' : x.val ^ 3 = 7 := by
        rw [aeval_def] at hx
        norm_num [apm_b00j01_poly] at hx
        exact sub_eq_zero.mp hx
      exact hx'.trans hα.symm }
  have hreal : Fintype.card ((apm_b00j01_poly ℚ).rootSet ℝ) = 1 :=
    Fintype.card_unique
  have hcomplex : Fintype.card ((apm_b00j01_poly ℚ).rootSet ℂ) = 3 := by
    rw [Polynomial.card_rootSet_eq_natDegree
      apm_b00j01_irreducible_rat.separable (IsAlgClosed.splits _)]
    norm_num [apm_b00j01_poly]
  omega

/-- Conjugating permutations along an equivalence is a multiplicative
equivalence of full permutation groups. -/
def apm_b00j01_permMulEquivCongr {A B : Type*} (e : A ≃ B) :
    Equiv.Perm A ≃* Equiv.Perm B where
  toEquiv := Equiv.permCongr e
  map_mul' σ τ := by
    ext b
    simp [Equiv.permCongr_apply]

/-- The prime-degree complex-root action identifies the canonical polynomial
Galois group with `S₃`. -/
noncomputable def apm_b00j01_canonicalGal_mulEquiv_S3 :
    (apm_b00j01_poly ℚ).Gal ≃* Equiv.Perm (Fin 3) := by
  letI : Fact (((apm_b00j01_poly ℚ).map (algebraMap ℚ ℂ)).Splits) :=
    ⟨IsAlgClosed.splits _⟩
  have hdeg : (apm_b00j01_poly ℚ).natDegree.Prime := by
    norm_num [apm_b00j01_poly]
  have hbij := Polynomial.Gal.galActionHom_bijective_of_prime_degree
    apm_b00j01_irreducible_rat hdeg apm_b00j01_rootSet_card_relation
  let actionEquiv := MulEquiv.ofBijective
    (Polynomial.Gal.galActionHom (apm_b00j01_poly ℚ) ℂ) hbij
  have hcard : Fintype.card ((apm_b00j01_poly ℚ).rootSet ℂ) = 3 := by
    rw [Polynomial.card_rootSet_eq_natDegree
      apm_b00j01_irreducible_rat.separable (IsAlgClosed.splits _)]
    norm_num [apm_b00j01_poly]
  let rootsEquiv : (apm_b00j01_poly ℚ).rootSet ℂ ≃ Fin 3 :=
    (Fintype.equivFin _).trans (finCongr hcard)
  exact actionEquiv.trans (apm_b00j01_permMulEquivCongr rootsEquiv)

/-- Splitting-field uniqueness transports the canonical `S₃` computation to
every abstract rational splitting field in the frozen statement. -/
lemma apm_b00j01_rational_aut_mulEquiv_S3
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (apm_b00j01_poly ℚ)] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3)) := by
  let e := Polynomial.IsSplittingField.algEquiv K (apm_b00j01_poly ℚ)
  exact ⟨(AlgEquiv.autCongr e).trans apm_b00j01_canonicalGal_mulEquiv_S3⟩

/-- The three transpositions of `S₃`, indexed by the point omitted from their
two-element support. -/
def apm_b00j01_transposition : Fin 3 → Equiv.Perm (Fin 3) :=
  ![Equiv.swap 1 2, Equiv.swap 0 2, Equiv.swap 0 1]

/-- The three order-two subgroups of `S₃`. -/
def apm_b00j01_orderTwoSubgroup (i : Fin 3) :
    Subgroup (Equiv.Perm (Fin 3)) where
  carrier := {g | g = 1 ∨ g = apm_b00j01_transposition i}
  one_mem' := Or.inl rfl
  mul_mem' := by
    fin_cases i <;> decide +revert
  inv_mem' := by
    fin_cases i <;> decide +revert

lemma apm_b00j01_orderTwoSubgroup_card (i : Fin 3) :
    Nat.card (apm_b00j01_orderTwoSubgroup i) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Or.inl rfl⟩,
    ⟨apm_b00j01_transposition i, Or.inr rfl⟩, ?_, ?_⟩
  · intro h
    have hv := congrArg Subtype.val h
    fin_cases i
    all_goals revert hv; decide
  · apply Set.eq_univ_of_forall
    intro g
    rw [Set.mem_insert_iff]
    rcases g.property with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

lemma apm_b00j01_transposition_ne_one (i : Fin 3) :
    apm_b00j01_transposition i ≠ 1 := by
  fin_cases i <;> decide

lemma apm_b00j01_orderTwoSubgroup_injective :
    Function.Injective apm_b00j01_orderTwoSubgroup := by
  intro i j
  classical
  intro h
  have hm : apm_b00j01_transposition i ∈ apm_b00j01_orderTwoSubgroup j := by
    rw [← h]
    exact Or.inr rfl
  change apm_b00j01_transposition i = 1 ∨
    apm_b00j01_transposition i = apm_b00j01_transposition j at hm
  rcases hm with hm | hm
  · exact (apm_b00j01_transposition_ne_one i hm).elim
  · fin_cases i <;> fin_cases j
    all_goals first | rfl | (revert hm; decide)

lemma apm_b00j01_alternatingGroup_card :
    Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num

lemma apm_b00j01_orderTwoSubgroup_not_normal (i : Fin 3) :
    ¬(apm_b00j01_orderTwoSubgroup i).Normal := by
  intro h
  let c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hm := h.conj_mem (apm_b00j01_transposition i) (Or.inr rfl)
    c
  change
    c * apm_b00j01_transposition i * c⁻¹ = 1 ∨
    c * apm_b00j01_transposition i * c⁻¹ = apm_b00j01_transposition i at hm
  fin_cases i
  all_goals revert hm; decide

lemma apm_b00j01_perm_cases (g : Equiv.Perm (Fin 3)) :
    g = 1 ∨ (∃ i, g = apm_b00j01_transposition i) ∨
      g = apm_b00j01_transposition 0 * apm_b00j01_transposition 1 ∨
      g = apm_b00j01_transposition 1 * apm_b00j01_transposition 0 := by
  revert g
  decide

lemma apm_b00j01_transposition_order (i : Fin 3) :
    orderOf (apm_b00j01_transposition i) = 2 := by
  apply (orderOf_eq_iff (by norm_num)).2
  constructor
  · fin_cases i <;> decide
  · intro m hm hm0
    interval_cases m
    all_goals fin_cases i <;> decide

lemma apm_b00j01_cycle_order :
    orderOf (apm_b00j01_transposition 0 * apm_b00j01_transposition 1) = 3 ∧
    orderOf (apm_b00j01_transposition 1 * apm_b00j01_transposition 0) = 3 := by
  constructor <;> apply (orderOf_eq_iff (by norm_num)).2 <;> constructor
  · decide
  · intro m hm hm0
    interval_cases m <;> decide
  · decide
  · intro m hm hm0
    interval_cases m <;> decide

lemma apm_b00j01_cycles_mem_alternating :
    apm_b00j01_transposition 0 * apm_b00j01_transposition 1 ∈
      alternatingGroup (Fin 3) ∧
    apm_b00j01_transposition 1 * apm_b00j01_transposition 0 ∈
      alternatingGroup (Fin 3) := by
  constructor <;> rw [Equiv.Perm.mem_alternatingGroup] <;> decide

/-- The complete subgroup lattice of `S₃`: trivial, alternating, one of the
three transposition subgroups, or the full group. -/
lemma apm_b00j01_S3_subgroup_classification
    (H : Subgroup (Equiv.Perm (Fin 3))) :
    H = ⊥ ∨ H = alternatingGroup (Fin 3) ∨
      (∃ i, H = apm_b00j01_orderTwoSubgroup i) ∨ H = ⊤ := by
  have hcardG : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    norm_num
  have hdvd : Nat.card H ∣ 6 := by
    simpa [hcardG] using H.card_subgroup_dvd_card
  have hpos : 0 < Nat.card H := Nat.card_pos
  have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  have hcases : Nat.card H = 1 ∨ Nat.card H = 2 ∨
      Nat.card H = 3 ∨ Nat.card H = 6 := by
    interval_cases hc : Nat.card H
    all_goals simp_all
  rcases hcases with h1 | h2 | h3 | h6
  · exact Or.inl (Subgroup.card_eq_one.mp h1)
  · right; right; left
    have hne : H ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at h2
      omega
    have hnle : ¬H ≤ ⊥ := fun hlebot ↦ hne (bot_unique hlebot)
    obtain ⟨g, hgH, hgnot⟩ := SetLike.not_le_iff_exists.mp hnle
    have hg1 : g ≠ 1 := by
      intro hg
      subst g
      exact hgnot (by simp)
    rcases apm_b00j01_perm_cases g with hg | ⟨i, hg⟩ | hg | hg
    · exact False.elim (hg1 hg)
    · subst g
      refine ⟨i, ?_⟩
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · intro x hx
        rcases hx with hx | hx
        · simp [hx]
        · simpa [hx] using hgH
      · rw [apm_b00j01_orderTwoSubgroup_card, h2]
    · subst g
      have hd3 := H.orderOf_dvd_natCard hgH
      rw [apm_b00j01_cycle_order.1, h2] at hd3
      norm_num at hd3
    · subst g
      have hd3 := H.orderOf_dvd_natCard hgH
      rw [apm_b00j01_cycle_order.2, h2] at hd3
      norm_num at hd3
  · right; left
    have hle : H ≤ alternatingGroup (Fin 3) := by
      intro g hgH
      rcases apm_b00j01_perm_cases g with hg | ⟨i, hg⟩ | hg | hg
      · rw [hg]
        exact Subgroup.one_mem _
      · subst g
        have hd2 := H.orderOf_dvd_natCard hgH
        rw [apm_b00j01_transposition_order, h3] at hd2
        norm_num at hd2
      · simpa [hg] using apm_b00j01_cycles_mem_alternating.1
      · simpa [hg] using apm_b00j01_cycles_mem_alternating.2
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [apm_b00j01_alternatingGroup_card, h3]
  · right; right; right
    exact H.eq_top_of_card_eq (h6.trans hcardG.symm)

/-- The fixed fields attached to the alternating subgroup and the three
transposition subgroups have degrees two and three, and the latter are
pairwise distinct. -/
lemma apm_b00j01_fixedField_degree_data
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (apm_b00j01_poly ℚ)] :
    ∃ (E₂ : IntermediateField ℚ K) (E₃ : Fin 3 → IntermediateField ℚ K),
      Module.finrank ℚ E₂ = 2 ∧ Function.Injective E₃ ∧
      ∀ i, Module.finrank ℚ (E₃ i) = 3 := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K (apm_b00j01_poly ℚ)
  letI : IsGalois ℚ K :=
    IsGalois.of_separable_splitting_field apm_b00j01_irreducible_rat.separable
  let e : (K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3) :=
    (apm_b00j01_rational_aut_mulEquiv_S3 K).some
  let H₂ : Subgroup (K ≃ₐ[ℚ] K) :=
    e.comapSubgroup (alternatingGroup (Fin 3))
  let H₃ (i : Fin 3) : Subgroup (K ≃ₐ[ℚ] K) :=
    e.comapSubgroup (apm_b00j01_orderTwoSubgroup i)
  let E₂ : IntermediateField ℚ K := IntermediateField.fixedField H₂
  let E₃ (i : Fin 3) : IntermediateField ℚ K := IntermediateField.fixedField (H₃ i)
  have htotal : Module.finrank ℚ K = 6 := by
    rw [← IsGalois.card_aut_eq_finrank]
    calc
      Nat.card (K ≃ₐ[ℚ] K) = Nat.card (Equiv.Perm (Fin 3)) :=
        Nat.card_congr e.toEquiv
      _ = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        norm_num
  have hcard_comap (H : Subgroup (Equiv.Perm (Fin 3))) :
      Nat.card (e.comapSubgroup H) = Nat.card H := by
    let f := e.toMonoidHom.subgroupComap H
    exact Nat.card_congr (Equiv.ofBijective f
      ⟨fun x y h ↦ Subtype.ext (e.injective (Subtype.ext_iff.mp h)),
        MonoidHom.subgroupComap_surjective_of_surjective e.toMonoidHom H e.surjective⟩)
  have hdeg₂ : Module.finrank ℚ E₂ = 2 := by
    have htower := Module.finrank_mul_finrank ℚ E₂ K
    have hext := IntermediateField.finrank_fixedField_eq_card H₂
    have hc : Nat.card H₂ = 3 := by
      exact (hcard_comap (alternatingGroup (Fin 3))).trans
        apm_b00j01_alternatingGroup_card
    dsimp [E₂] at htower
    rw [hext, hc, htotal] at htower
    nlinarith [Module.finrank_pos (R := ℚ) (M := E₂)]
  have hdeg₃ (i : Fin 3) : Module.finrank ℚ (E₃ i) = 3 := by
    have htower := Module.finrank_mul_finrank ℚ (E₃ i) K
    have hext := IntermediateField.finrank_fixedField_eq_card (H₃ i)
    have hc : Nat.card (H₃ i) = 2 := by
      exact (hcard_comap (apm_b00j01_orderTwoSubgroup i)).trans
        (apm_b00j01_orderTwoSubgroup_card i)
    rw [hext, hc, htotal] at htower
    nlinarith [Module.finrank_pos (R := ℚ) (M := E₃ i)]
  have hinj : Function.Injective E₃ := by
    intro i j hij
    apply apm_b00j01_orderTwoSubgroup_injective
    apply e.comapSubgroup.injective
    have hh := congrArg IntermediateField.fixingSubgroup hij
    simpa [E₃, IntermediateField.fixingSubgroup_fixedField] using hh
  exact ⟨E₂, E₃, hdeg₂, hinj, hdeg₃⟩

/-- Normality of the alternating subgroup and nonnormality of the three
transposition subgroups give exactly the requested Galois statuses of their
fixed fields. -/
lemma apm_b00j01_fixedField_galois_data
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (apm_b00j01_poly ℚ)] :
    ∃ (E₂ : IntermediateField ℚ K) (E₃ : Fin 3 → IntermediateField ℚ K),
      @IsGalois ℚ _ E₂ _ E₂.algebra' ∧
        ∀ i, ¬@IsGalois ℚ _ (E₃ i) _ (E₃ i).algebra' := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K (apm_b00j01_poly ℚ)
  letI : IsGalois ℚ K :=
    IsGalois.of_separable_splitting_field apm_b00j01_irreducible_rat.separable
  let e : (K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3) :=
    (apm_b00j01_rational_aut_mulEquiv_S3 K).some
  let H₂ : Subgroup (K ≃ₐ[ℚ] K) :=
    e.comapSubgroup (alternatingGroup (Fin 3))
  let H₃ (i : Fin 3) : Subgroup (K ≃ₐ[ℚ] K) :=
    e.comapSubgroup (apm_b00j01_orderTwoSubgroup i)
  let E₂ : IntermediateField ℚ K := IntermediateField.fixedField H₂
  let E₃ (i : Fin 3) : IntermediateField ℚ K := IntermediateField.fixedField (H₃ i)
  have hg₂ : @IsGalois ℚ _ E₂ _ E₂.algebra' := by
    have hn : H₂.Normal := by
      exact Subgroup.Normal.comap (inferInstance : (alternatingGroup (Fin 3)).Normal)
        e.toMonoidHom
    letI : H₂.Normal := hn
    dsimp only [E₂]
    exact IsGalois.of_fixedField_normal_subgroup H₂
  have hng₃ (i : Fin 3) : ¬@IsGalois ℚ _ (E₃ i) _ (E₃ i).algebra' := by
    intro hg
    letI : Algebra ℚ (E₃ i) := (E₃ i).algebra'
    letI : IsGalois ℚ (E₃ i) := hg
    have hnfix : (E₃ i).fixingSubgroup.Normal :=
      IsGalois.fixingSubgroup_normal_of_isGalois (E₃ i)
    have hn : (H₃ i).Normal := by
      simpa [E₃, IntermediateField.fixingSubgroup_fixedField] using hnfix
    have hnmap := hn.map e.toMonoidHom e.surjective
    have htarget : (apm_b00j01_orderTwoSubgroup i).Normal := by
      dsimp only [H₃] at hnmap
      rw [MulEquiv.coe_comapSubgroup,
        Subgroup.map_comap_eq_self_of_surjective e.surjective] at hnmap
      exact hnmap
    exact apm_b00j01_orderTwoSubgroup_not_normal i htarget
  exact ⟨E₂, E₃, hg₂, hng₃⟩

/-- Why this unblocks the rational-field conjunct of `apm_b00j01`: it is the
missing concrete Galois-correspondence computation for the splitting field of
`X³ - 7`, including the exhaustive list of intermediate fields and their
Galois status. -/
theorem apm_b00J01_bridge_1
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K (apm_b00j01_poly ℚ)] :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ (E₂ : IntermediateField ℚ K) (E₃ : Fin 3 → IntermediateField ℚ K),
        Module.finrank ℚ E₂ = 2 ∧
        Function.Injective E₃ ∧
        (∀ i, Module.finrank ℚ (E₃ i) = 3) ∧
        (∀ E : IntermediateField ℚ K,
          E = ⊥ ∨ E = E₂ ∨ (∃ i, E = E₃ i) ∨ E = ⊤) ∧
        IsGalois ℚ E₂ ∧
        (∀ i, ¬IsGalois ℚ (E₃ i)) := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K (apm_b00j01_poly ℚ)
  letI : IsGalois ℚ K :=
    IsGalois.of_separable_splitting_field apm_b00j01_irreducible_rat.separable
  let e : (K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3) :=
    (apm_b00j01_rational_aut_mulEquiv_S3 K).some
  let H₂ : Subgroup (K ≃ₐ[ℚ] K) :=
    e.comapSubgroup (alternatingGroup (Fin 3))
  let H₃ (i : Fin 3) : Subgroup (K ≃ₐ[ℚ] K) :=
    e.comapSubgroup (apm_b00j01_orderTwoSubgroup i)
  let E₂ : IntermediateField ℚ K := IntermediateField.fixedField H₂
  let E₃ (i : Fin 3) : IntermediateField ℚ K := IntermediateField.fixedField (H₃ i)
  have htotal : Module.finrank ℚ K = 6 := by
    rw [← IsGalois.card_aut_eq_finrank]
    calc
      Nat.card (K ≃ₐ[ℚ] K) = Nat.card (Equiv.Perm (Fin 3)) :=
        Nat.card_congr e.toEquiv
      _ = 6 := by
        rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
        norm_num
  have hcard_comap (H : Subgroup (Equiv.Perm (Fin 3))) :
      Nat.card (e.comapSubgroup H) = Nat.card H := by
    let f := e.toMonoidHom.subgroupComap H
    exact Nat.card_congr (Equiv.ofBijective f
      ⟨fun x y h ↦ Subtype.ext (e.injective (Subtype.ext_iff.mp h)),
        MonoidHom.subgroupComap_surjective_of_surjective e.toMonoidHom H e.surjective⟩)
  have hdeg₂ : Module.finrank ℚ E₂ = 2 := by
    have htower := Module.finrank_mul_finrank ℚ E₂ K
    have hext := IntermediateField.finrank_fixedField_eq_card H₂
    have hc : Nat.card H₂ = 3 := by
      exact (hcard_comap (alternatingGroup (Fin 3))).trans
        apm_b00j01_alternatingGroup_card
    dsimp [E₂] at htower
    rw [hext, hc, htotal] at htower
    nlinarith [Module.finrank_pos (R := ℚ) (M := E₂)]
  have hdeg₃ (i : Fin 3) : Module.finrank ℚ (E₃ i) = 3 := by
    have htower := Module.finrank_mul_finrank ℚ (E₃ i) K
    have hext := IntermediateField.finrank_fixedField_eq_card (H₃ i)
    have hc : Nat.card (H₃ i) = 2 := by
      exact (hcard_comap (apm_b00j01_orderTwoSubgroup i)).trans
        (apm_b00j01_orderTwoSubgroup_card i)
    rw [hext, hc, htotal] at htower
    nlinarith [Module.finrank_pos (R := ℚ) (M := E₃ i)]
  have hinj : Function.Injective E₃ := by
    intro i j hij
    apply apm_b00j01_orderTwoSubgroup_injective
    apply e.comapSubgroup.injective
    have hh := congrArg IntermediateField.fixingSubgroup hij
    simpa [E₃, IntermediateField.fixingSubgroup_fixedField] using hh
  have hexhaust (E : IntermediateField ℚ K) :
      E = ⊥ ∨ E = E₂ ∨ (∃ i, E = E₃ i) ∨ E = ⊤ := by
    rcases apm_b00j01_S3_subgroup_classification
        (e.mapSubgroup E.fixingSubgroup) with hbot | halt | hthree | htop
    · right; right; right
      rw [← IsGalois.fixedField_fixingSubgroup (K := E)]
      have hfix : E.fixingSubgroup = ⊥ := by
        apply e.mapSubgroup.injective
        simpa using hbot
      rw [hfix, IntermediateField.fixedField_bot]
    · right; left
      rw [← IsGalois.fixedField_fixingSubgroup (K := E)]
      have hfix : E.fixingSubgroup = H₂ := by
        apply e.mapSubgroup.injective
        dsimp only [H₂]
        rw [MulEquiv.coe_mapSubgroup, MulEquiv.coe_comapSubgroup,
          Subgroup.map_comap_eq_self_of_surjective e.surjective]
        exact halt
      exact congrArg IntermediateField.fixedField hfix
    · rcases hthree with ⟨i, hi⟩
      right; right; left
      refine ⟨i, ?_⟩
      rw [← IsGalois.fixedField_fixingSubgroup (K := E)]
      have hfix : E.fixingSubgroup = H₃ i := by
        apply e.mapSubgroup.injective
        dsimp only [H₃]
        rw [MulEquiv.coe_mapSubgroup, MulEquiv.coe_comapSubgroup,
          Subgroup.map_comap_eq_self_of_surjective e.surjective]
        exact hi
      exact congrArg IntermediateField.fixedField hfix
    · left
      rw [← IsGalois.fixedField_fixingSubgroup (K := E)]
      have hfix : E.fixingSubgroup = ⊤ := by
        apply e.mapSubgroup.injective
        simpa using htop
      rw [hfix, IsGalois.fixedField_top]
  have hg₂ : @IsGalois ℚ _ E₂ _ E₂.algebra' := by
    have hn : H₂.Normal := by
      exact Subgroup.Normal.comap (inferInstance : (alternatingGroup (Fin 3)).Normal)
        e.toMonoidHom
    letI : H₂.Normal := hn
    dsimp only [E₂]
    exact IsGalois.of_fixedField_normal_subgroup H₂
  have hng₃ (i : Fin 3) : ¬@IsGalois ℚ _ (E₃ i) _ (E₃ i).algebra' := by
    intro hg
    letI : Algebra ℚ (E₃ i) := (E₃ i).algebra'
    letI : IsGalois ℚ (E₃ i) := hg
    have hnfix : (E₃ i).fixingSubgroup.Normal :=
      IsGalois.fixingSubgroup_normal_of_isGalois (E₃ i)
    have hn : (H₃ i).Normal := by
      simpa [E₃, IntermediateField.fixingSubgroup_fixedField] using hnfix
    have hnmap := hn.map e.toMonoidHom e.surjective
    have htarget : (apm_b00j01_orderTwoSubgroup i).Normal := by
      dsimp only [H₃] at hnmap
      rw [MulEquiv.coe_comapSubgroup,
        Subgroup.map_comap_eq_self_of_surjective e.surjective] at hnmap
      exact hnmap
    exact apm_b00j01_orderTwoSubgroup_not_normal i htarget
  have hg₂' : IsGalois ℚ E₂ := by
    convert hg₂ using 1
    all_goals exact Subsingleton.elim _ _
  have hng₃' (i : Fin 3) : ¬IsGalois ℚ (E₃ i) := by
    intro hg
    apply hng₃ i
    convert hg using 1
    all_goals exact Subsingleton.elim _ _
  exact ⟨apm_b00j01_rational_aut_mulEquiv_S3 K, E₂, E₃, hdeg₂, hinj,
    hdeg₃, hexhaust, hg₂', hng₃'⟩

/-- Why this unblocks the real-field conjunct of `apm_b00j01`: it identifies
the real splitting field as the quadratic extension obtained by adjoining a
nonreal root and computes its two-element automorphism group. -/
theorem apm_b00J01_bridge_2
    (L : Type*) [Field L] [Algebra ℝ L]
    [IsSplittingField ℝ L (apm_b00j01_poly ℝ)] :
    Nonempty ((L ≃ₐ[ℝ] L) ≃* Multiplicative (ZMod 2)) := by
  exact apm_b00j01_real_bridge_of_complex_splitting
    apm_b00j01_complex_isSplittingField L

/-- Why this unblocks the finite-field conjunct of `apm_b00j01`: the exact
degree says that an irreducible cubic's root field already contains all three
roots, and the second conjunct transports the canonical degree-three
finite-field Frobenius action to the arbitrary splitting field. -/
theorem apm_b00J01_bridge_3
    [Fact (Nat.Prime 13)]
    (M : Type*) [Field M] [Algebra (ZMod 13) M]
    [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))] :
    Module.finrank (ZMod 13) M = 3 ∧
      Nonempty ((M ≃ₐ[ZMod 13] M) ≃* Multiplicative (ZMod 3)) := by
  letI : IsSplittingField (ZMod 13) M (X ^ 3 - C 7) := by
    simpa [apm_b00j01_poly] using
      (inferInstance : IsSplittingField (ZMod 13) M
        (apm_b00j01_poly (ZMod 13)))
  have hζ := apm_b00j01_primitiveRoot_three_mod13
  have hfin : Module.finrank (ZMod 13) M = 3 := by
    apply finrank_of_isSplittingField_X_pow_sub_C
      (hζ := ⟨3, (mem_primitiveRoots (by norm_num : 0 < 3)).2 hζ⟩)
      apm_b00j01_irreducible_mod13
  refine ⟨hfin, ?_⟩
  exact ⟨autEquivZmod apm_b00j01_irreducible_mod13 M hζ⟩

theorem apm_b00j01 :
    (∀ (K : Type*) [Field K] [Algebra ℚ K]
        [IsSplittingField ℚ K (apm_b00j01_poly ℚ)],
      Nonempty ((K ≃ₐ[ℚ] K) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ (E₂ : IntermediateField ℚ K) (E₃ : Fin 3 → IntermediateField ℚ K),
        Module.finrank ℚ E₂ = 2 ∧
        Function.Injective E₃ ∧
        (∀ i, Module.finrank ℚ (E₃ i) = 3) ∧
        (∀ E : IntermediateField ℚ K,
          E = ⊥ ∨ E = E₂ ∨ (∃ i, E = E₃ i) ∨ E = ⊤) ∧
        IsGalois ℚ E₂ ∧
        (∀ i, ¬IsGalois ℚ (E₃ i))) ∧
    (∀ (L : Type*) [Field L] [Algebra ℝ L]
        [IsSplittingField ℝ L (apm_b00j01_poly ℝ)],
      Nonempty ((L ≃ₐ[ℝ] L) ≃* Multiplicative (ZMod 2))) ∧
    (∀ [Fact (Nat.Prime 13)] (M : Type*) [Field M] [Algebra (ZMod 13) M]
        [IsSplittingField (ZMod 13) M (apm_b00j01_poly (ZMod 13))],
      Nonempty ((M ≃ₐ[ZMod 13] M) ≃* Multiplicative (ZMod 3))) := by
  /-
  PARTIAL boundary (closer hop 3). This hop applies the general theorem
  `Polynomial.Irreducible.natDegree_dvd_finrank` to the arbitrary splitting
  field.  The compiled helpers
  `apm_b00j01_three_dvd_finiteField_finrank` and
  `apm_b00j01_three_dvd_finiteField_card_aut` prove respectively that its
  degree and its Galois automorphism-group cardinality are divisible by three.
  Thus the lower-bound half of the exact degree-three calculation is closed.

  Source inspection found `IsSplittingField.algEquiv`, which identifies two
  splitting fields of the *same polynomial*, and the canonical
  `GaloisField 13 3`, which is presented instead as a splitting field of
  `X^(13^3)-X`.  No theorem in the finite-field or splitting-field APIs shows
  directly that the roots of this particular irreducible cubic all lie in the
  degree-three root field, so the needed upper bound `finrank ≤ 3` and the
  transport to the canonical Frobenius equivalence remain open.

  The real splitting-field identification and the much larger rational `S₃`
  Galois-correspondence enumeration also remain open. Searches included
  `LEMMA-INDEX.md`, all construction targets, splitting-field uniqueness,
  finite Galois fields, cubic minpolys, and prior Galois siblings; none packages
  either classification required by the frozen conjunction.

  This closer found the missing finite-field dependency in solved sibling
  `b94J03`: `finrank_of_isSplittingField_X_pow_sub_C` and `autEquivZmod`.
  The new lemma `apm_b00j01_primitiveRoot_three_mod13` proves that
  `3 : ZMod 13` is a primitive cube root of unity, so those Kummer results
  close `apm_b00J01_bridge_3` completely.  The residue computation was also
  changed from `native_decide` to kernel-checked `decide`.  Only the rational
  `S₃` correspondence and real quadratic splitting-field bridges remain.
  -/
  exact
    ⟨fun K _ _ _ ↦ apm_b00J01_bridge_1 K,
      fun L _ _ _ ↦ apm_b00J01_bridge_2 L,
      fun M _ _ _ ↦ (apm_b00J01_bridge_3 M).2⟩
