import Mathlib

/-!
# APM b97J03

## Statement repairs

None.

## Encoding questions

None. The number `r` is the finite cardinality of the set of complex roots
lying in the actual intermediate field `ℚ(α)`, and the Galois group is the
automorphism group of an arbitrary splitting field.
-/

open Polynomial


/-- The number of roots of `P` contained in `ℚ(α)`. -/
noncomputable def apm_b97j03_rootCount (P : Polynomial ℚ) (α : ℂ) : ℕ :=
  Set.ncard {z : ℂ |
    (P.map (algebraMap ℚ ℂ)).IsRoot z ∧
      z ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ)}

/-- The polynomial `X⁶ - 2`. -/
noncomputable def apm_b97j03_special : Polynomial ℚ :=
  X ^ 6 - C 2

noncomputable def apm_b97j03_specialInt : Polynomial ℤ := X ^ 6 - C 2

noncomputable def apm_b97j03_sqrtTwoInt : Polynomial ℤ := X ^ 2 - C 2

lemma apm_b97j03_specialInt_irreducible : Irreducible apm_b97j03_specialInt := by
  have hdeg : apm_b97j03_specialInt.natDegree = 6 := by
    rw [apm_b97j03_specialInt, natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · norm_num
  have hm : apm_b97j03_specialInt.Monic := by
    exact monic_X_pow_sub_C (2 : ℤ) (by norm_num : 6 ≠ 0)
  have he : apm_b97j03_specialInt.IsEisensteinAt (Ideal.span ({2} : Set ℤ)) := by
    apply hm.isEisensteinAt_of_mem_of_notMem
    · exact Ideal.span_singleton_ne_top (by norm_num [Int.isUnit_iff])
    · intro n hn
      have hn' : n < 6 := by simpa [hdeg] using hn
      rw [Ideal.mem_span_singleton]
      simp only [apm_b97j03_specialInt, coeff_sub, coeff_X_pow, coeff_C]
      split_ifs <;> norm_num <;> omega
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      norm_num [apm_b97j03_specialInt]
  exact he.irreducible
    ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2 (by norm_num))
    hm.isPrimitive (by simp [hdeg])

lemma apm_b97j03_special_irreducible : Irreducible apm_b97j03_special := by
  have hm : apm_b97j03_specialInt.IsPrimitive :=
    (monic_X_pow_sub_C (2 : ℤ) (by norm_num : 6 ≠ 0)).isPrimitive
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm).mp
    apm_b97j03_specialInt_irreducible
  simpa [apm_b97j03_specialInt, apm_b97j03_special] using h

lemma apm_b97j03_sqrtTwoInt_irreducible : Irreducible apm_b97j03_sqrtTwoInt := by
  have hdeg : apm_b97j03_sqrtTwoInt.natDegree = 2 := by
    rw [apm_b97j03_sqrtTwoInt, natDegree_sub_eq_left_of_natDegree_lt]
    · simp
    · norm_num
  have hm : apm_b97j03_sqrtTwoInt.Monic :=
    monic_X_pow_sub_C (2 : ℤ) (by norm_num : 2 ≠ 0)
  have he : apm_b97j03_sqrtTwoInt.IsEisensteinAt
      (Ideal.span ({2} : Set ℤ)) := by
    apply hm.isEisensteinAt_of_mem_of_notMem
    · exact Ideal.span_singleton_ne_top (by norm_num [Int.isUnit_iff])
    · intro n hn
      have hn' : n < 2 := by simpa [hdeg] using hn
      rw [Ideal.mem_span_singleton]
      simp only [apm_b97j03_sqrtTwoInt, coeff_sub, coeff_X_pow, coeff_C]
      split_ifs <;> norm_num <;> omega
    · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      norm_num [apm_b97j03_sqrtTwoInt]
  exact he.irreducible
    ((Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).2 (by norm_num))
    hm.isPrimitive (by simp [hdeg])

lemma apm_b97j03_sqrtTwo_irreducible : Irreducible (X ^ 2 - C 2 : ℚ[X]) := by
  have hm : apm_b97j03_sqrtTwoInt.IsPrimitive :=
    (monic_X_pow_sub_C (2 : ℤ) (by norm_num : 2 ≠ 0)).isPrimitive
  have h := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hm).mp
    apm_b97j03_sqrtTwoInt_irreducible
  simpa [apm_b97j03_sqrtTwoInt] using h

lemma apm_b97j03_special_minpoly {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    minpoly ℚ α = apm_b97j03_special := by
  symm
  apply minpoly.eq_of_irreducible_of_monic apm_b97j03_special_irreducible
  · simpa [Polynomial.IsRoot, aeval_def] using hα
  · exact monic_X_pow_sub_C (2 : ℚ) (by norm_num : 6 ≠ 0)

lemma apm_b97j03_finrank_adjoin_root {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({α} : Set ℂ)) = 6 := by
  have hi : IsIntegral ℚ α := ⟨apm_b97j03_special,
    monic_X_pow_sub_C (2 : ℚ) (by norm_num : 6 ≠ 0), by
      simpa [Polynomial.IsRoot, aeval_def] using hα⟩
  rw [IntermediateField.adjoin.finrank hi,
    apm_b97j03_special_minpoly hα]
  norm_num [apm_b97j03_special]

/-- The restricted root count is bounded by the degree, independently of the
Galois normalizer argument needed for divisibility. -/
lemma apm_b97j03_rootCount_le_natDegree (P : Polynomial ℚ) (α : ℂ)
    (hP : P ≠ 0) :
    apm_b97j03_rootCount P α ≤ P.natDegree := by
  let T : Set ℂ := {z : ℂ |
    (P.map (algebraMap ℚ ℂ)).IsRoot z ∧
      z ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ)}
  have hsub : T ⊆ P.rootSet ℂ := by
    intro z hz
    exact (Polynomial.mem_rootSet_of_ne hP).2 (by
      simpa [Polynomial.IsRoot, aeval_def] using hz.1)
  change Set.ncard T ≤ P.natDegree
  exact (Set.ncard_le_ncard hsub (Polynomial.rootSet_finite P ℂ)).trans
    (Polynomial.ncard_rootSet_le P ℂ)

lemma apm_b97j03_irreducible_isRoot_iff_minpoly_isRoot
    (P : Polynomial ℚ) (α z : ℂ) (hP : Irreducible P)
    (hα : (P.map (algebraMap ℚ ℂ)).IsRoot α) :
    (P.map (algebraMap ℚ ℂ)).IsRoot z ↔
      ((minpoly ℚ α).map (algebraMap ℚ ℂ)).IsRoot z := by
  have hαeval : Polynomial.aeval α P = 0 := by
    simpa [Polynomial.IsRoot, aeval_def] using hα
  have hPmin := minpoly.Irreducible.eq_minpoly hP hαeval
  rw [hPmin, Polynomial.map_mul]
  simp only [Polynomial.IsRoot, eval_mul, Polynomial.map_C, eval_C]
  have hlc : algebraMap ℚ ℂ P.leadingCoeff ≠ 0 := by
    simpa using (algebraMap ℚ ℂ).injective.ne
      (leadingCoeff_ne_zero.mpr hP.ne_zero)
  rw [mul_eq_zero, or_iff_right hlc]

lemma apm_b97j03_finrank_adjoin_irreducible_root
    (P : Polynomial ℚ) (α : ℂ) (hP : Irreducible P)
    (hα : (P.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({α} : Set ℂ)) = P.natDegree := by
  have hαeval : Polynomial.aeval α P = 0 := by
    simpa [Polynomial.IsRoot, aeval_def] using hα
  have hi : IsIntegral ℚ α := ⟨P * C P.leadingCoeff⁻¹,
    monic_mul_leadingCoeff_inv hP.ne_zero, by
      rw [eval₂_mul]
      have hz : eval₂ (algebraMap ℚ ℂ) α P = 0 := by
        simpa [aeval_def] using hαeval
      rw [hz, zero_mul]⟩
  rw [IntermediateField.adjoin.finrank hi]
  have hPmin := minpoly.eq_of_irreducible hP hαeval
  rw [← hPmin, natDegree_mul hP.ne_zero
    (C_ne_zero.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hP.ne_zero)))]
  simp

lemma apm_b97j03_card_aut_dvd_finrank
    (F E : Type*) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] :
    Nat.card (E ≃ₐ[F] E) ∣ Module.finrank F E := by
  let H : Subgroup (E ≃ₐ[F] E) := ⊤
  have ht := Module.finrank_mul_finrank F (IntermediateField.fixedField H) E
  rw [IntermediateField.finrank_fixedField_eq_card] at ht
  have hcard : Nat.card H = Nat.card (E ≃ₐ[F] E) := by
    exact Nat.card_congr (Equiv.Set.univ (E ≃ₐ[F] E))
  rw [hcard] at ht
  rw [mul_comm] at ht
  exact ⟨Module.finrank F (IntermediateField.fixedField H), ht.symm⟩

lemma apm_b97j03_rootCount_eq_card_aut
    (P : Polynomial ℚ) (α : ℂ) (hP : Irreducible P)
    (hα : (P.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97j03_rootCount P α =
      Nat.card ((IntermediateField.adjoin ℚ ({α} : Set ℂ)) ≃ₐ[ℚ]
        (IntermediateField.adjoin ℚ ({α} : Set ℂ))) := by
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({α} : Set ℂ)
  let T : Set ℂ := {z : ℂ | (P.map (algebraMap ℚ ℂ)).IsRoot z ∧ z ∈ E}
  have hαeval : Polynomial.aeval α P = 0 := by
    simpa [Polynomial.IsRoot, aeval_def] using hα
  have hi : IsIntegral ℚ α := ⟨P * C P.leadingCoeff⁻¹,
    monic_mul_leadingCoeff_inv hP.ne_zero, by
      rw [eval₂_mul]
      have hz : eval₂ (algebraMap ℚ ℂ) α P = 0 := by
        simpa [aeval_def] using hαeval
      rw [hz, zero_mul]⟩
  letI : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hi
  let eRoots : T ≃ {x : E // x ∈ (minpoly ℚ α).aroots E} :=
    { toFun := fun z => ⟨⟨z.1, z.2.2⟩, by
        rw [Polynomial.mem_aroots]
        refine ⟨minpoly.ne_zero hi, ?_⟩
        have hc := (apm_b97j03_irreducible_isRoot_iff_minpoly_isRoot
          P α z.1 hP hα).mp z.2.1
        have he : ((minpoly ℚ α).map (algebraMap ℚ E)).IsRoot
            (⟨z.1, z.2.2⟩ : E) := by
          apply (Polynomial.isRoot_map_iff E.subtype.injective).mp
          simpa [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ E ℂ] using hc
        simpa [Polynomial.IsRoot, aeval_def] using he⟩
      invFun := fun x => ⟨x.1.1, by
        refine ⟨(apm_b97j03_irreducible_isRoot_iff_minpoly_isRoot
          P α x.1.1 hP hα).mpr ?_, x.1.2⟩
        have he : ((minpoly ℚ α).map (algebraMap ℚ E)).IsRoot x.1 := by
          simpa [Polynomial.IsRoot, aeval_def] using (Polynomial.mem_aroots.mp x.2).2
        have hc := he.map (f := E.subtype)
        simpa [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ E ℂ] using hc⟩
      left_inv := by intro z; rfl
      right_inv := by intro x; rfl }
  have hcard : Set.ncard T = Nat.card (E ≃ₐ[ℚ] E) := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (eRoots.trans ?_)
    let eHom : (E →ₐ[ℚ] E) ≃ {x : E // x ∈ (minpoly ℚ α).aroots E} := by
      simpa [E] using (IntermediateField.algHomAdjoinIntegralEquiv ℚ (K := E) hi)
    exact eHom.symm.trans
      (Algebra.IsAlgebraic.algEquivEquivAlgHom ℚ E).symm
  simpa [apm_b97j03_rootCount, T, E] using hcard

lemma apm_b97j03_special_natDegree : apm_b97j03_special.natDegree = 6 := by
  norm_num [apm_b97j03_special]

lemma apm_b97j03_special_rootCount_le_six (α : ℂ) :
    apm_b97j03_rootCount apm_b97j03_special α ≤ 6 := by
  rw [← apm_b97j03_special_natDegree]
  apply apm_b97j03_rootCount_le_natDegree
  intro h
  have hc := congrArg (fun p : ℚ[X] => p.coeff 6) h
  norm_num [apm_b97j03_special] at hc

lemma apm_b97j03_special_root_pow_six {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    α ^ 6 = 2 := by
  have h : α ^ 6 - 2 = 0 := by
    simpa [apm_b97j03_special, Polynomial.IsRoot] using hα
  exact sub_eq_zero.mp h

lemma apm_b97j03_special_root_cube_minpoly {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    minpoly ℚ (α ^ 3) = (X ^ 2 - C 2 : ℚ[X]) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic apm_b97j03_sqrtTwo_irreducible
  · rw [aeval_def]
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    rw [← pow_mul, show 3 * 2 = 6 by norm_num,
      apm_b97j03_special_root_pow_six hα]
    norm_num
  · exact monic_X_pow_sub_C (2 : ℚ) (by norm_num : 2 ≠ 0)

lemma apm_b97j03_finrank_adjoin_root_cube {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ ({α ^ 3} : Set ℂ)) = 2 := by
  have hi : IsIntegral ℚ (α ^ 3) := ⟨X ^ 2 - C 2,
    monic_X_pow_sub_C (2 : ℚ) (by norm_num : 2 ≠ 0), by
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
      rw [← pow_mul, show 3 * 2 = 6 by norm_num,
        apm_b97j03_special_root_pow_six hα]
      norm_num⟩
  rw [IntermediateField.adjoin.finrank hi,
    apm_b97j03_special_root_cube_minpoly hα]
  norm_num

lemma apm_b97j03_adjoin_cube_le_adjoin_root (α : ℂ) :
    IntermediateField.adjoin ℚ ({α ^ 3} : Set ℂ) ≤
      IntermediateField.adjoin ℚ ({α} : Set ℂ) := by
  rw [IntermediateField.adjoin_le_iff]
  intro z hz
  rcases hz with rfl
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ α) 3

lemma apm_b97j03_relfinrank_cube_root {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    IntermediateField.relfinrank
      (IntermediateField.adjoin ℚ ({α ^ 3} : Set ℂ))
      (IntermediateField.adjoin ℚ ({α} : Set ℂ)) = 3 := by
  have htower := IntermediateField.finrank_bot_mul_relfinrank
    (apm_b97j03_adjoin_cube_le_adjoin_root α)
  rw [apm_b97j03_finrank_adjoin_root_cube hα,
    apm_b97j03_finrank_adjoin_root hα] at htower
  omega

lemma apm_b97j03_special_root_ne_zero {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) : α ≠ 0 := by
  intro hzero
  have hpow := apm_b97j03_special_root_pow_six hα
  rw [hzero, zero_pow (by norm_num : 6 ≠ 0)] at hpow
  norm_num at hpow

/-- A fixed primitive sixth root of unity used to enumerate all complex roots
of the special polynomial. -/
noncomputable def apm_b97j03_zeta6 : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / 6)

lemma apm_b97j03_zeta6_primitive : IsPrimitiveRoot apm_b97j03_zeta6 6 := by
  exact Complex.isPrimitiveRoot_exp 6 (by norm_num)

lemma apm_b97j03_zeta6_pow_three : apm_b97j03_zeta6 ^ 3 = -1 := by
  rw [apm_b97j03_zeta6, ← Complex.exp_nat_mul]
  convert Complex.exp_pi_mul_I using 1
  push_cast
  ring_nf

lemma apm_b97j03_zeta6_quadratic :
    apm_b97j03_zeta6 ^ 2 - apm_b97j03_zeta6 + 1 = 0 := by
  have hne : apm_b97j03_zeta6 ≠ -1 := by
    intro h
    have hp : apm_b97j03_zeta6 ^ 1 = apm_b97j03_zeta6 ^ 3 := by
      simpa [h] using apm_b97j03_zeta6_pow_three.symm
    have := apm_b97j03_zeta6_primitive.pow_inj (by norm_num : 1 < 6)
      (by norm_num : 3 < 6) hp
    norm_num at this
  have hfac : (apm_b97j03_zeta6 + 1) *
      (apm_b97j03_zeta6 ^ 2 - apm_b97j03_zeta6 + 1) = 0 := by
    rw [show (apm_b97j03_zeta6 + 1) *
      (apm_b97j03_zeta6 ^ 2 - apm_b97j03_zeta6 + 1) =
        apm_b97j03_zeta6 ^ 3 + 1 by ring,
      apm_b97j03_zeta6_pow_three]
    norm_num
  exact (mul_eq_zero.mp hfac).resolve_left (by simpa [add_eq_zero_iff_eq_neg] using hne)

lemma apm_b97j03_zeta6_sq_quadratic :
    (apm_b97j03_zeta6 ^ 2) ^ 2 + apm_b97j03_zeta6 ^ 2 + 1 = 0 := by
  calc
    (apm_b97j03_zeta6 ^ 2) ^ 2 + apm_b97j03_zeta6 ^ 2 + 1 =
        (apm_b97j03_zeta6 ^ 2 - apm_b97j03_zeta6 + 1) *
          (apm_b97j03_zeta6 ^ 2 + apm_b97j03_zeta6 + 1) := by ring
    _ = 0 := by rw [apm_b97j03_zeta6_quadratic, zero_mul]

lemma apm_b97j03_zeta6_not_mem_realField :
    apm_b97j03_zeta6 ∉
      (Complex.ofRealHom.toRatAlgHom.fieldRange : Set ℂ) := by
  intro hmem
  rcases hmem with ⟨r, hr⟩
  have hq := apm_b97j03_zeta6_quadratic
  rw [← hr] at hq
  have hre := congrArg Complex.re hq
  norm_num [pow_two, Complex.mul_re] at hre
  nlinarith [sq_nonneg (r - (1 / 2 : ℝ))]

lemma apm_b97j03_zeta6_sq_not_mem_realField :
    apm_b97j03_zeta6 ^ 2 ∉
      (Complex.ofRealHom.toRatAlgHom.fieldRange : Set ℂ) := by
  intro hsq
  apply apm_b97j03_zeta6_not_mem_realField
  have heq : apm_b97j03_zeta6 = apm_b97j03_zeta6 ^ 2 + 1 := by
    linear_combination -apm_b97j03_zeta6_quadratic
  rw [heq]
  exact Complex.ofRealHom.toRatAlgHom.fieldRange.add_mem hsq
    Complex.ofRealHom.toRatAlgHom.fieldRange.one_mem

lemma apm_b97j03_special_root_cube_sq {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    (α ^ 3) ^ 2 = 2 := by
  rw [← pow_mul]
  norm_num [apm_b97j03_special_root_pow_six hα]

noncomputable def apm_b97j03_realField : IntermediateField ℚ ℂ :=
  Complex.ofRealHom.toRatAlgHom.fieldRange

lemma apm_b97j03_special_root_cube_mem_realField {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    α ^ 3 ∈ apm_b97j03_realField := by
  let x : ℂ := α ^ 3
  have hsq : x ^ 2 = 2 := apm_b97j03_special_root_cube_sq hα
  have hre := congrArg Complex.re hsq
  have him := congrArg Complex.im hsq
  have him0 : x.im = 0 := by
    by_contra hn
    have hre0 : x.re = 0 := by
      norm_num [pow_two, Complex.mul_im] at him
      have hprod : x.re * x.im = 0 := by nlinarith
      exact (mul_eq_zero.mp hprod).resolve_right hn
    norm_num [pow_two, Complex.mul_re] at hre
    nlinarith [sq_nonneg x.im]
  have hxreal : x = (x.re : ℂ) := by
    apply Complex.ext <;> simp [him0]
  change x ∈ Complex.ofRealHom.toRatAlgHom.fieldRange
  exact ⟨x.re, hxreal.symm⟩

lemma apm_b97j03_adjoin_cube_le_realField {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    IntermediateField.adjoin ℚ ({α ^ 3} : Set ℂ) ≤ apm_b97j03_realField := by
  rw [IntermediateField.adjoin_le_iff]
  intro z hz
  rcases hz with rfl
  exact apm_b97j03_special_root_cube_mem_realField hα

lemma apm_b97j03_zeta6_not_mem_adjoin_cube {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97j03_zeta6 ∉
      (IntermediateField.adjoin ℚ ({α ^ 3} : Set ℂ) : Set ℂ) := by
  intro hmem
  exact apm_b97j03_zeta6_not_mem_realField
    (apm_b97j03_adjoin_cube_le_realField hα hmem)

lemma apm_b97j03_zeta6_sq_not_mem_adjoin_cube {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97j03_zeta6 ^ 2 ∉
      (IntermediateField.adjoin ℚ ({α ^ 3} : Set ℂ) : Set ℂ) := by
  intro hmem
  exact apm_b97j03_zeta6_sq_not_mem_realField
    (apm_b97j03_adjoin_cube_le_realField hα hmem)

/-- For any chosen root `α`, the special polynomial factors into the six
root-of-unity multiples of `α`.  This makes the total root list explicit; the
remaining issue is which factors lie in the embedded field `ℚ(α)`. -/
lemma apm_b97j03_special_factorization {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97j03_special.map (algebraMap ℚ ℂ) =
      ∏ i ∈ Finset.range 6,
        (X - C (apm_b97j03_zeta6 ^ i * α)) := by
  have hpow := apm_b97j03_special_root_pow_six hα
  simpa [apm_b97j03_special, apm_b97j03_zeta6] using
    (X_pow_sub_C_eq_prod apm_b97j03_zeta6_primitive
      (by norm_num : 0 < 6) hpow)

/-- Relative to any chosen root `α`, every other complex root is one of the
six root-of-unity multiples occurring in the explicit factorization. -/
lemma apm_b97j03_special_root_eq_zeta6_pow_mul {α z : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α)
    (hz : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot z) :
    ∃ i ∈ Finset.range 6, z = apm_b97j03_zeta6 ^ i * α := by
  rw [Polynomial.IsRoot] at hz
  rw [apm_b97j03_special_factorization hα, eval_prod] at hz
  obtain ⟨i, hi, hiz⟩ := Finset.prod_eq_zero_iff.mp hz
  refine ⟨i, hi, sub_eq_zero.mp ?_⟩
  simpa using hiz

/-- The six entries in the relative root list are pairwise distinct. -/
lemma apm_b97j03_zeta6_pow_mul_injective {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α)
    {i j : ℕ} (hi : i < 6) (hj : j < 6)
    (hij : apm_b97j03_zeta6 ^ i * α = apm_b97j03_zeta6 ^ j * α) :
    i = j := by
  apply apm_b97j03_zeta6_primitive.pow_inj hi hj
  exact mul_right_cancel₀ (apm_b97j03_special_root_ne_zero hα) hij

/-- Every entry of the explicit relative root list is indeed a root. -/
lemma apm_b97j03_zeta6_pow_mul_isRoot {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α)
    {i : ℕ} (hi : i < 6) :
    (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot
      (apm_b97j03_zeta6 ^ i * α) := by
  rw [Polynomial.IsRoot, apm_b97j03_special_factorization hα, eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hi)
  simp

/-- The second evident conjugate of every root is again a root. -/
lemma apm_b97j03_special_neg_root {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot (-α) := by
  have hpow := apm_b97j03_special_root_pow_six hα
  rw [Polynomial.IsRoot]
  simp [apm_b97j03_special, show (-α) ^ 6 = α ^ 6 by ring, hpow]

/-- Both evident roots lie in the actual embedded field generated by `α`. -/
lemma apm_b97j03_special_roots_mem_adjoin {α : ℂ}
    : α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) ∧
      -α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) := by
  have hmem : α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) :=
    IntermediateField.subset_adjoin (F := ℚ) (S := ({α} : Set ℂ)) (by simp)
  exact ⟨hmem, neg_mem hmem⟩

/-- For every chosen root, the two evident roots already give the lower bound
in the final exact root-count computation. -/
lemma apm_b97j03_two_le_special_rootCount {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    2 ≤ apm_b97j03_rootCount apm_b97j03_special α := by
  let T : Set ℂ := {z : ℂ |
    (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot z ∧
      z ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ)}
  have hmem := apm_b97j03_special_roots_mem_adjoin (α := α)
  have hsub : ({α, -α} : Set ℂ) ⊆ T := by
    intro z hz
    rcases hz with (rfl | rfl)
    · exact ⟨hα, hmem.1⟩
    · exact ⟨apm_b97j03_special_neg_root hα, hmem.2⟩
  have hne : α ≠ -α := by
    intro h
    have htwo : (2 : ℂ) * α = 0 := by linear_combination h
    have : α = 0 := (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    exact apm_b97j03_special_root_ne_zero hα this
  have hpne : apm_b97j03_special ≠ 0 := by
    intro h
    have hc := congrArg (fun p : ℚ[X] => p.coeff 6) h
    norm_num [apm_b97j03_special] at hc
  have hTfin : T.Finite := (Polynomial.rootSet_finite apm_b97j03_special ℂ).subset (by
    intro z hz
    exact (Polynomial.mem_rootSet_of_ne hpne).2 (by
      simpa [Polynomial.IsRoot, aeval_def] using hz.1))
  change 2 ≤ Set.ncard T
  calc
    2 = Set.ncard ({α, -α} : Set ℂ) := by simp [hne]
    _ ≤ Set.ncard T := Set.ncard_le_ncard hsub hTfin

/-- Why this unblocks the divisibility clause of `apm_b97j03`: this is the
normalizer--stabilizer orbit computation for the transitive Galois action on
the roots of an irreducible rational polynomial, expressed in the frozen
embedded-field root count. -/
theorem apm_b97J03_bridge_1
    (P : Polynomial ℚ) (α : ℂ) (hP : Irreducible P)
    (hα : (P.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97j03_rootCount P α ∣ P.natDegree := by
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({α} : Set ℂ)
  have hαeval : Polynomial.aeval α P = 0 := by
    simpa [Polynomial.IsRoot, aeval_def] using hα
  have hi : IsIntegral ℚ α := ⟨P * C P.leadingCoeff⁻¹,
    monic_mul_leadingCoeff_inv hP.ne_zero, by
      rw [eval₂_mul]
      have hz : eval₂ (algebraMap ℚ ℂ) α P = 0 := by
        simpa [aeval_def] using hαeval
      rw [hz, zero_mul]⟩
  letI : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hi
  rw [apm_b97j03_rootCount_eq_card_aut P α hP hα]
  rw [← apm_b97j03_finrank_adjoin_irreducible_root P α hP hα]
  exact apm_b97j03_card_aut_dvd_finrank ℚ E

/-- Why this unblocks the abelian clause of `apm_b97j03`: when the splitting
field's Galois group is abelian, the stabilizer of one root is normal, so its
normalizer orbit contains every root. -/
theorem apm_b97J03_bridge_2
    (P : Polynomial ℚ) (α : ℂ) (hP : Irreducible P)
    (hα : (P.map (algebraMap ℚ ℂ)).IsRoot α)
    (K : Type*) [Field K] [Algebra ℚ K] [IsSplittingField ℚ K P]
    (hcomm : ∀ σ τ : K ≃ₐ[ℚ] K, σ * τ = τ * σ) :
    apm_b97j03_rootCount P α = P.natDegree := by
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({α} : Set ℂ)
  have hαeval : Polynomial.aeval α P = 0 := by
    simpa [Polynomial.IsRoot, aeval_def] using hα
  have hi : IsIntegral ℚ α := ⟨P * C P.leadingCoeff⁻¹,
    monic_mul_leadingCoeff_inv hP.ne_zero, by
      rw [eval₂_mul]
      have hz : eval₂ (algebraMap ℚ ℂ) α P = 0 := by
        simpa [aeval_def] using hαeval
      rw [hz, zero_mul]⟩
  have hsplits : ((minpoly ℚ α).map (algebraMap ℚ K)).Splits := by
    apply (IsSplittingField.splits K P).of_dvd
    · exact Polynomial.map_ne_zero hP.ne_zero
    · exact (Polynomial.map_dvd_map (algebraMap ℚ K) (algebraMap ℚ K).injective
        (minpoly.monic hi)).mpr (minpoly.dvd ℚ α hαeval)
  letI : IsGalois ℚ K := IsGalois.of_separable_splitting_field hP.separable
  letI : IsAbelianGalois ℚ K := { is_comm.comm := hcomm }
  let f : E →ₐ[ℚ] K := Classical.choice <|
    IntermediateField.nonempty_algHom_adjoin_of_splits (K := K) (S := ({α} : Set ℂ)) <| by
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨hi, hsplits⟩
  letI : FiniteDimensional ℚ E := IntermediateField.adjoin.finiteDimensional hi
  letI : IsAbelianGalois ℚ E := IsAbelianGalois.of_algHom f
  rw [apm_b97j03_rootCount_eq_card_aut P α hP hα]
  rw [IsGalois.card_aut_eq_finrank]
  exact apm_b97j03_finrank_adjoin_irreducible_root P α hP hα

/-- The irreducible pure-sextic calculation at its smallest useful boundary:
among the six explicit relative roots, only indices zero and three can lie in
the field generated by the chosen root. -/
lemma apm_b97j03_zeta6_pow_mem_adjoin_of_mul_mem {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α)
    {i : ℕ}
    (hmem : apm_b97j03_zeta6 ^ i * α ∈
      IntermediateField.adjoin ℚ ({α} : Set ℂ)) :
    apm_b97j03_zeta6 ^ i ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) := by
  have ha : α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) :=
    IntermediateField.subset_adjoin (F := ℚ) (S := ({α} : Set ℂ)) (by simp)
  have hainv : α⁻¹ ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) := inv_mem ha
  have hprod := mul_mem hmem hainv
  simpa [apm_b97j03_special_root_ne_zero hα] using hprod

/-- The genuine arithmetic core of the special case.  The pure sextic field
contains neither generator of the non-real quadratic cyclotomic extension. -/
theorem apm_b97j03_zeta6_not_mem_and_sq_not_mem {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97j03_zeta6 ∉ IntermediateField.adjoin ℚ ({α} : Set ℂ) ∧
      apm_b97j03_zeta6 ^ 2 ∉ IntermediateField.adjoin ℚ ({α} : Set ℂ) := by
  let B : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({α ^ 3} : Set ℂ)
  let E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({α} : Set ℂ)
  have hBE : B ≤ E := apm_b97j03_adjoin_cube_le_adjoin_root α
  let L : IntermediateField B ℂ := IntermediateField.extendScalars hBE
  have hfin : Module.finrank B L = 3 := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hBE]
    exact apm_b97j03_relfinrank_cube_root hα
  letI : Module.Free B L := Module.Free.of_divisionRing B L
  have hfinite : Module.Finite B L := Module.finite_of_finrank_pos (by omega)
  letI : Module.Finite B L := hfinite
  have exclude (x : ℂ) (hxE : x ∈ E) (hxB : x ∉ (B : Set ℂ))
      (p : Polynomial B) (hpmon : p.Monic) (hpdeg : p.natDegree = 2)
      (hpzero : Polynomial.aeval (⟨x, hxE⟩ : L) p = 0) : False := by
    let xL : L := ⟨x, hxE⟩
    have hxi : IsIntegral B xL := ⟨p, hpmon, hpzero⟩
    have hdvd : (minpoly B xL).natDegree ∣ 3 := by
      simpa [hfin] using minpoly.degree_dvd hxi
    have hle : (minpoly B xL).natDegree ≤ 2 := by
      rw [← hpdeg]
      exact natDegree_le_of_dvd (minpoly.dvd B xL hpzero) hpmon.ne_zero
    have hne1 : (minpoly B xL).natDegree ≠ 1 := by
      intro hdeg
      have hdegree : (minpoly B xL).degree = 1 := by
        rw [degree_eq_natDegree (minpoly.ne_zero hxi), hdeg]
        norm_num
      rcases minpoly.degree_eq_one_iff.mp hdegree with ⟨b, hb⟩
      apply hxB
      have hbx : (b : ℂ) = x := congrArg Subtype.val hb
      rw [← hbx]
      exact b.property
    have hpos : 0 < (minpoly B xL).natDegree := minpoly.natDegree_pos hxi
    have heq : (minpoly B xL).natDegree = 2 := by omega
    rw [heq] at hdvd
    norm_num at hdvd
  constructor
  · intro hz
    let zL : L := ⟨apm_b97j03_zeta6, hz⟩
    let p : Polynomial B := X ^ 2 - X + 1
    apply exclude apm_b97j03_zeta6 hz (apm_b97j03_zeta6_not_mem_adjoin_cube hα)
      p (by dsimp [p]; monicity; norm_num)
      (by dsimp [p]; compute_degree; norm_num)
    dsimp [p]
    simp only [Polynomial.aeval_def, eval₂_add, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    apply Subtype.ext
    exact apm_b97j03_zeta6_quadratic
  · intro hz
    let zL : L := ⟨apm_b97j03_zeta6 ^ 2, hz⟩
    let p : Polynomial B := X ^ 2 + X + 1
    apply exclude (apm_b97j03_zeta6 ^ 2) hz
      (apm_b97j03_zeta6_sq_not_mem_adjoin_cube hα) p
      (by dsimp [p]; monicity; norm_num)
      (by dsimp [p]; compute_degree; norm_num)
    dsimp [p]
    simp only [Polynomial.aeval_def, eval₂_add, eval₂_pow, eval₂_X, eval₂_one]
    apply Subtype.ext
    exact apm_b97j03_zeta6_sq_quadratic

/-- The irreducible pure-sextic/cyclotomic intersection calculation: no
non-real sixth root of unity belongs to the chosen pure sextic field. -/
theorem apm_b97J03_zeta6_pow_mul_mem_adjoin {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α)
    {i : ℕ} (hi : i < 6)
    (hmem : apm_b97j03_zeta6 ^ i * α ∈
      IntermediateField.adjoin ℚ ({α} : Set ℂ)) :
    i = 0 ∨ i = 3 := by
  have hzeta := apm_b97j03_zeta6_pow_mem_adjoin_of_mul_mem hα hmem
  have hnot := apm_b97j03_zeta6_not_mem_and_sq_not_mem hα
  have hsix : apm_b97j03_zeta6 ^ 6 = 1 :=
    apm_b97j03_zeta6_primitive.pow_eq_one
  interval_cases i
  · exact Or.inl rfl
  · exact (hnot.1 (by simpa using hzeta)).elim
  · exact (hnot.2 hzeta).elim
  · exact Or.inr rfl
  · have hp := pow_mem hzeta 2
    have heq : (apm_b97j03_zeta6 ^ 4) ^ 2 = apm_b97j03_zeta6 ^ 2 := by
      rw [← pow_mul, show 4 * 2 = 2 + 6 by norm_num, pow_add, hsix, mul_one]
    rw [heq] at hp
    exact (hnot.2 hp).elim
  · have hp := pow_mem hzeta 4
    have heq : (apm_b97j03_zeta6 ^ 5) ^ 4 = apm_b97j03_zeta6 ^ 2 := by
      rw [← pow_mul, show 5 * 4 = 2 + 6 + 6 + 6 by norm_num, pow_add,
        pow_add, pow_add, hsix]
      simp
    rw [heq] at hp
    exact (hnot.2 hp).elim

/-- The exact Kummer-field exclusion needed by the special case: an ambient
root which lies in the embedded pure sextic field is one of the two evident
roots. -/
theorem apm_b97J03_special_root_mem_adjoin_iff {α z : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α)
    (hz : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot z)
    (hzmem : z ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ)) :
    z = α ∨ z = -α := by
  obtain ⟨i, hi, rfl⟩ := apm_b97j03_special_root_eq_zeta6_pow_mul hα hz
  rcases apm_b97J03_zeta6_pow_mul_mem_adjoin hα
      (Finset.mem_range.mp hi) hzmem with rfl | rfl
  · left
    simp
  · right
    rw [apm_b97j03_zeta6_pow_three]
    simp

/-- Why this unblocks the special-polynomial clause of `apm_b97j03`: the
compiled lower bound already supplies the roots `±α`, while the exact
membership classification bounds the restricted root set by that pair. -/
theorem apm_b97J03_bridge_3
    {α : ℂ}
    (hα : (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97j03_rootCount apm_b97j03_special α ≤ 2 := by
  let T : Set ℂ := {z : ℂ |
    (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot z ∧
      z ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ)}
  have hsub : T ⊆ ({α, -α} : Set ℂ) := by
    intro z hz
    exact apm_b97J03_special_root_mem_adjoin_iff hα hz.1 hz.2
  change Set.ncard T ≤ 2
  calc
    Set.ncard T ≤ Set.ncard ({α, -α} : Set ℂ) :=
      Set.ncard_le_ncard hsub (by simp)
    _ ≤ Set.ncard ({-α} : Set ℂ) + 1 := Set.ncard_insert_le α {-α}
    _ = 2 := by simp

theorem apm_b97j03 :
    (∀ (P : Polynomial ℚ) (α : ℂ),
      Irreducible P → (P.map (algebraMap ℚ ℂ)).IsRoot α →
      apm_b97j03_rootCount P α ∣ P.natDegree ∧
      (∀ (K : Type*) [Field K] [Algebra ℚ K] [IsSplittingField ℚ K P],
        (∀ σ τ : K ≃ₐ[ℚ] K, σ * τ = τ * σ) →
        apm_b97j03_rootCount P α = P.natDegree)) ∧
    (∀ α : ℂ, (apm_b97j03_special.map (algebraMap ℚ ℂ)).IsRoot α →
      apm_b97j03_rootCount apm_b97j03_special α = 2) := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib's splitting-field and Kummer APIs
  provide root-set generation (`IsSplittingField.adjoin_rootSet`) and formulas
  such as `X_pow_sub_C_eq_prod`, but local source and proved-sibling searches
  found no theorem identifying the roots lying in `ℚ(α)` with cosets of the
  normalizer of the stabilizer of `α`.

  Formalizing the divisibility clause requires choosing and comparing an
  arbitrary splitting field with the concrete complex roots, proving the
  transitive Galois action for irreducible `P`, identifying
  `IntermediateField.adjoin ℚ {α}` with the stabilizer fixed field, and turning
  the restricted root-set cardinality into `[N_G(H) : H]`. The abelian clause
  then needs this transport to show all roots lie in the complex adjoin.
  Finally, the `X^6 - 2` clause quantifies over every complex root, so the usual
  positive-real-root argument is insufficient without a proof that each
  embedded field generated by a nonreal root contains exactly its two roots
  `±α`. No searched Kummer lemma supplies that `Set.ncard` conclusion. The
  statement appears mathematically sound.

  Closer hop 1 closes the uniform lower-bound half of the special-polynomial
  clause. `apm_b97j03_special_root_pow_six` extracts `α⁶ = 2`,
  `apm_b97j03_special_root_ne_zero` proves every root is nonzero,
  `apm_b97j03_special_neg_root` proves `-α` is again a root, and
  `apm_b97j03_special_roots_mem_adjoin` places both roots in the actual
  embedded field `ℚ(α)`. Finally `apm_b97j03_two_le_special_rootCount` proves
  the custom `Set.ncard` is at least two, using root-set finiteness and the
  distinctness of `α` and `-α`. This works for every complex root, avoiding
  the invalid positive-real-root specialization noted above.

  Searches of `LEMMA-INDEX.md`, closed artifacts, `ConstructionTargets/`, the
  Kummer API, and root-set/adjoin lemmas still found no packaged upper bound
  excluding the other four roots from `ℚ(α)`. That upper bound and the general
  normalizer/stabilizer correspondence are the remaining bridges.

  Closer hop 2 proves the strongest root-set bound available without that
  correspondence. `apm_b97j03_rootCount_le_natDegree` embeds the custom set
  into Mathlib's finite `Polynomial.rootSet` and applies
  `Polynomial.ncard_rootSet_le`. The special polynomial's degree is computed
  as six, yielding `apm_b97j03_special_rootCount_le_six`; together with hop
  1, every special count is now bounded between two and six. This does not
  exclude the four nonreal-root-of-unity multiples from the particular
  embedded field `ℚ(α)`. Searches of minimal-polynomial, power-basis, Kummer,
  and normalizer APIs found no packaged theorem making that exclusion or
  identifying the general count with a normalizer index, so those bridges
  remain open.

  Closer hop 3 constructs a fixed primitive sixth root
  `apm_b97j03_zeta6` and proves `apm_b97j03_special_factorization`: for every
  chosen root `α`, the mapped polynomial is exactly the product of the six
  linear factors with roots `ζ^i α`.  Thus the complete ambient complex root
  list is now compiled, narrowing the special-case obstruction precisely to
  proving that only the `i = 0,3` factors lie in `ℚ(α)`.  Searches of embedded
  power-basis coordinates and rational Kummer intersections still found no
  packaged exclusion theorem; the general normalizer-index bridge also
  remains open.
  -/
  constructor
  · intro P α hP hα
    refine ⟨apm_b97J03_bridge_1 P α hP hα, ?_⟩
    intro K _ _ _ hcomm
    exact apm_b97J03_bridge_2 P α hP hα K hcomm
  · intro α hα
    exact Nat.le_antisymm (apm_b97J03_bridge_3 hα)
      (apm_b97j03_two_le_special_rootCount hα)
