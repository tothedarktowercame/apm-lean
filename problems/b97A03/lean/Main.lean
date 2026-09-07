import Mathlib

/-!
# APM b97A03 — the splitting field and subfields of `X⁶ + 3`

## Statement repairs

None.

## Encoding notes

For a chosen complex root `α`, `ℚ(α)` is represented by
`IntermediateField.adjoin ℚ {α}` inside `ℂ`.  Completeness of the subfield list
is stated for every intermediate field of `ℂ/ℚ` contained in `ℚ(α)`, so the
actual embedded fields—not merely their degrees—are retained.
-/

open Set Polynomial

noncomputable def apm_b97a03_polynomial : ℚ[X] :=
  Polynomial.X ^ 6 + Polynomial.C 3

noncomputable def apm_b97a03_field (α : ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {α}

noncomputable def apm_b97a03_zeta (α : ℂ) : ℂ :=
  (1 + α ^ 3) / 2

/-- The defining equation satisfied by any chosen complex root. -/
lemma apm_b97a03_root_pow_six {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    α ^ 6 = -3 := by
  have h : α ^ 6 + 3 = 0 := by
    simpa [apm_b97a03_polynomial, Polynomial.IsRoot] using hα
  exact eq_neg_of_add_eq_zero_left h

/-- The cubic power of a root is a square root of `-3`. -/
lemma apm_b97a03_root_pow_three_sq {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (α ^ 3) ^ 2 = -3 := by
  rw [← pow_mul, show 3 * 2 = 6 by norm_num]
  exact apm_b97a03_root_pow_six hα

/-- The element extracted from a root satisfies the sixth-root-of-unity
quadratic relation used to generate the other roots. -/
lemma apm_b97a03_zeta_relation {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_zeta α ^ 2 - apm_b97a03_zeta α + 1 = 0 := by
  have h := apm_b97a03_root_pow_three_sq hα
  rw [apm_b97a03_zeta]
  field_simp
  linear_combination h

/-- The derived element is a sixth root of unity with cube `-1`. -/
lemma apm_b97a03_zeta_pow_three {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_zeta α ^ 3 = -1 := by
  have h := apm_b97a03_zeta_relation hα
  apply eq_neg_of_add_eq_zero_left
  linear_combination (apm_b97a03_zeta α + 1) * h

lemma apm_b97a03_zeta_pow_six {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_zeta α ^ 6 = 1 := by
  rw [show 6 = 3 * 2 by norm_num, pow_mul, apm_b97a03_zeta_pow_three hα]
  norm_num

/-- The derived sixth root of unity is primitive, not merely a root of
unity. -/
lemma apm_b97a03_zeta_primitive {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IsPrimitiveRoot (apm_b97a03_zeta α) 6 := by
  let z := apm_b97a03_zeta α
  have hrel : z ^ 2 - z + 1 = 0 := apm_b97a03_zeta_relation hα
  have h3 : z ^ 3 = -1 := apm_b97a03_zeta_pow_three hα
  have h6 : z ^ 6 = 1 := apm_b97a03_zeta_pow_six hα
  have ho : orderOf z = 6 := (orderOf_eq_iff (by norm_num : 0 < 6)).2 (by
    constructor
    · exact h6
    · intro m hm hm0 heq
      interval_cases m
      · have hz : z = 1 := by simpa only [pow_one] using heq
        rw [hz] at h3
        norm_num at h3
      · have hz2 : z ^ 2 = 1 := heq
        have hz : z = 2 := by linear_combination -hrel + hz2
        rw [hz] at h3
        norm_num at h3
      · rw [h3] at heq
        norm_num at heq
      · have hz2 : z ^ 2 = 1 := by
          calc z ^ 2 = z ^ 4 * z ^ 2 := by rw [heq, one_mul]
               _ = z ^ 6 := by ring
               _ = 1 := h6
        have hz : z = 2 := by linear_combination -hrel + hz2
        rw [hz] at h3
        norm_num at h3
      · have hz : z = 1 := by
          calc z = z ^ 5 * z := by rw [heq, one_mul]
               _ = z ^ 6 := by ring
               _ = 1 := h6
        rw [hz] at h3
        norm_num at h3)
  rw [← ho]
  exact IsPrimitiveRoot.orderOf z

/-- The six candidate roots obtained from a chosen root are pairwise
distinct. -/
lemma apm_b97a03_candidate_roots_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective
      (fun k : Fin 6 => apm_b97a03_zeta α ^ (k : ℕ) * α) := by
  have ha : α ≠ 0 := by
    intro ha
    have hpow := apm_b97a03_root_pow_six hα
    rw [ha] at hpow
    norm_num at hpow
  intro i j hij
  apply Fin.ext
  exact (apm_b97a03_zeta_primitive hα).pow_inj i.isLt j.isLt
    (mul_right_cancel₀ ha hij)

/-- The root of unity extracted from `α` belongs to the same generated
intermediate field. -/
lemma apm_b97a03_zeta_mem_field {α : ℂ} :
    apm_b97a03_zeta α ∈ apm_b97a03_field α := by
  unfold apm_b97a03_zeta apm_b97a03_field
  apply IntermediateField.div_mem
  · apply IntermediateField.add_mem
    · exact IntermediateField.one_mem _
    · have ha : α ∈ IntermediateField.adjoin ℚ ({α} : Set ℂ) :=
        IntermediateField.subset_adjoin ℚ {α} (by simp)
      simpa [pow_succ] using
        IntermediateField.mul_mem _ (IntermediateField.mul_mem _ ha ha) ha
  · exact IntermediateField.natCast_mem _ 2

/-- Multiplying a chosen root by any power of the derived sixth root of unity
again gives a root. -/
lemma apm_b97a03_zeta_mul_root {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : ℕ) :
    (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot
      (apm_b97a03_zeta α ^ k * α) := by
  have hz := apm_b97a03_zeta_pow_six hα
  have ha := apm_b97a03_root_pow_six hα
  have hpow : (apm_b97a03_zeta α ^ k * α) ^ 6 = -3 := by
    rw [mul_pow, ← pow_mul, show k * 6 = 6 * k by omega, pow_mul, hz, one_pow, ha,
      one_mul]
  simp [apm_b97a03_polynomial, Polynomial.IsRoot, hpow]

lemma apm_b97a03_zeta_mul_root_mem_field {α : ℂ} (k : ℕ) :
    apm_b97a03_zeta α ^ k * α ∈ apm_b97a03_field α := by
  have hz := apm_b97a03_zeta_mem_field (α := α)
  have ha : α ∈ apm_b97a03_field α := by
    exact IntermediateField.subset_adjoin ℚ {α} (by simp)
  apply IntermediateField.mul_mem
  · induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        exact IntermediateField.mul_mem _ ih hz
  · exact ha

/-- Why this unblocks `apm_b97a03`: this is the independent arithmetic input
needed for the first conjunct; it can be proved by Eisenstein at `3`. -/
theorem apm_b97A03_bridge_1 :
    Irreducible apm_b97a03_polynomial := by
  let f : ℤ[X] := Polynomial.X ^ 6 + Polynomial.C 3
  have hmonic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_add_C (3 : ℤ) (by norm_num : 6 ≠ 0))
  have hf : f.IsEisensteinAt (Ideal.span {3}) := by
    constructor
    · rw [hmonic.leadingCoeff]
      norm_num [Ideal.mem_span_singleton]
    · intro n hn
      rw [show f.natDegree = 6 by simpa [f] using
        (Polynomial.natDegree_X_pow_add_C :
          (Polynomial.X ^ 6 + Polynomial.C (3 : ℤ)).natDegree = 6)] at hn
      interval_cases n <;>
        norm_num [f, Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Ideal.mem_span_singleton]
    · rw [show f.coeff 0 = 3 by simp [f], Ideal.span_singleton_pow]
      norm_num [Ideal.mem_span_singleton]
  have hp : (Ideal.span ({3} : Set ℤ)).IsPrime := by
    apply (Ideal.span_singleton_prime (by norm_num : (3 : ℤ) ≠ 0)).2
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  have hprim : f.IsPrimitive := hmonic.isPrimitive
  have hirr : Irreducible f := hf.irreducible hp hprim (by
    rw [show f.natDegree = 6 by simpa [f] using
      (Polynomial.natDegree_X_pow_add_C :
        (Polynomial.X ^ 6 + Polynomial.C (3 : ℤ)).natDegree = 6)]
    norm_num)
  have hmap : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hirr
  simpa [apm_b97a03_polynomial, f] using hmap

/-- The six candidates exhaust all complex roots. -/
lemma apm_b97a03_root_exhaustion {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    ∀ z : ℂ,
      (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot z →
        ∃ k : Fin 6, z = apm_b97a03_zeta α ^ (k : ℕ) * α := by
  intro z hz
  have hfac := X_pow_sub_C_eq_prod
    (apm_b97a03_zeta_primitive hα) (by norm_num : 0 < 6)
    (apm_b97a03_root_pow_six hα)
  have hz' : (Polynomial.X ^ 6 - Polynomial.C (-3 : ℂ)).IsRoot z := by
    simpa [apm_b97a03_polynomial, Polynomial.IsRoot] using hz
  rw [hfac] at hz'
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, Finset.prod_eq_zero_iff] at hz'
  obtain ⟨k, hk, heq⟩ := hz'
  refine ⟨⟨k, by simpa using hk⟩, ?_⟩
  simpa using heq

/-- Why this unblocks `apm_b97a03`: it identifies every complex root with one
of the six compiled candidates and packages the resulting splitting-field
statement in Mathlib's exact API. -/
theorem apm_b97A03_bridge_2 {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (∀ z : ℂ,
        (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot z →
          ∃ k : Fin 6, z = apm_b97a03_zeta α ^ (k : ℕ) * α) ∧
      Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
        apm_b97a03_polynomial := by
  have hexhaust := apm_b97a03_root_exhaustion hα
  refine ⟨hexhaust, ?_⟩
  have halg : (DivisionRing.toRatAlgebra : Algebra ℚ (apm_b97a03_field α)) =
      (apm_b97a03_field α).algebra := Subsingleton.elim _ _
  rw [halg]
  rw [IntermediateField.isSplittingField_iff]
  have hsC : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).Splits := by
    simpa [apm_b97a03_polynomial] using
      (X_pow_sub_C_splits_of_isPrimitiveRoot
        (apm_b97a03_zeta_primitive hα) (apm_b97a03_root_pow_six hα))
  constructor
  · apply IntermediateField.splits_of_splits hsC
    intro z hz
    obtain ⟨k, rfl⟩ := hexhaust z (by
      simpa [Polynomial.IsRoot, Polynomial.aeval_def] using
        (Polynomial.mem_rootSet'.mp hz).2)
    exact apm_b97a03_zeta_mul_root_mem_field k
  · apply le_antisymm
    · rw [apm_b97a03_field, IntermediateField.adjoin_le_iff]
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst z
      apply IntermediateField.subset_adjoin ℚ
      rw [Polynomial.mem_rootSet']
      exact ⟨by
        simpa [apm_b97a03_polynomial] using
          (Polynomial.monic_X_pow_add_C (3 : ℂ) (by norm_num : 6 ≠ 0)).ne_zero, by
        simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hα⟩
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := hexhaust z (by
        simpa [Polynomial.IsRoot, Polynomial.aeval_def] using
          (Polynomial.mem_rootSet'.mp hz).2)
      exact apm_b97a03_zeta_mul_root_mem_field k

lemma apm_b97a03_minpoly {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    minpoly ℚ α = apm_b97a03_polynomial := by
  symm
  apply minpoly.eq_of_irreducible_of_monic apm_b97A03_bridge_1
  · simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hα
  · exact Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 6 ≠ 0)

lemma apm_b97a03_isIntegral {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IsIntegral ℚ α := by
  refine ⟨apm_b97a03_polynomial,
    Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 6 ≠ 0), ?_⟩
  simpa [Polynomial.IsRoot, Polynomial.aeval_def] using hα

lemma apm_b97a03_finrank {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ (apm_b97a03_field α) = 6 := by
  rw [apm_b97a03_field, IntermediateField.adjoin.finrank
    (apm_b97a03_isIntegral hα), apm_b97a03_minpoly hα]
  exact Polynomial.natDegree_X_pow_add_C

lemma apm_b97a03_isGalois {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IsGalois ℚ (apm_b97a03_field α) := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  exact IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable

lemma apm_b97a03_card_aut {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Nat.card (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) = 6 := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) := apm_b97a03_isGalois hα
  rw [IsGalois.card_aut_eq_finrank]
  exact apm_b97a03_finrank hα

noncomputable def apm_b97a03_cubic : ℚ[X] :=
  Polynomial.X ^ 3 + Polynomial.C 3

noncomputable def apm_b97a03_beta (α : ℂ) (k : Fin 3) : ℂ :=
  apm_b97a03_zeta α ^ (2 * (k : ℕ)) * α ^ 2

lemma apm_b97a03_cubic_irreducible : Irreducible apm_b97a03_cubic := by
  let f : ℤ[X] := Polynomial.X ^ 3 + Polynomial.C 3
  have hmonic : f.Monic := by
    simpa [f] using (Polynomial.monic_X_pow_add_C (3 : ℤ) (by norm_num : 3 ≠ 0))
  have hf : f.IsEisensteinAt (Ideal.span {3}) := by
    constructor
    · rw [hmonic.leadingCoeff]
      norm_num [Ideal.mem_span_singleton]
    · intro n hn
      rw [show f.natDegree = 3 by simpa [f] using
        (Polynomial.natDegree_X_pow_add_C :
          (Polynomial.X ^ 3 + Polynomial.C (3 : ℤ)).natDegree = 3)] at hn
      interval_cases n <;>
        norm_num [f, Polynomial.coeff_add, Polynomial.coeff_X_pow,
          Ideal.mem_span_singleton]
    · rw [show f.coeff 0 = 3 by simp [f], Ideal.span_singleton_pow]
      norm_num [Ideal.mem_span_singleton]
  have hp : (Ideal.span ({3} : Set ℤ)).IsPrime := by
    apply (Ideal.span_singleton_prime (by norm_num : (3 : ℤ) ≠ 0)).2
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  have hprim : f.IsPrimitive := hmonic.isPrimitive
  have hirr : Irreducible f := hf.irreducible hp hprim (by
    rw [show f.natDegree = 3 by simpa [f] using
      (Polynomial.natDegree_X_pow_add_C :
        (Polynomial.X ^ 3 + Polynomial.C (3 : ℤ)).natDegree = 3)]
    norm_num)
  have hmap : Irreducible (f.map (Int.castRingHom ℚ)) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp hirr
  simpa [apm_b97a03_cubic, f] using hmap

lemma apm_b97a03_beta_root {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 3) :
    (apm_b97a03_cubic.map (algebraMap ℚ ℂ)).IsRoot
      (apm_b97a03_beta α k) := by
  have hz := apm_b97a03_zeta_pow_six hα
  have ha := apm_b97a03_root_pow_six hα
  have hp : (apm_b97a03_beta α k) ^ 3 = -3 := by
    rw [apm_b97a03_beta, mul_pow, ← pow_mul, ← pow_mul]
    norm_num only [mul_assoc]
    rw [show 2 * ((k : ℕ) * 3) = 6 * (k : ℕ) by omega, pow_mul, hz, one_pow,
      ha, one_mul]
  simp [apm_b97a03_cubic, Polynomial.IsRoot, hp]

lemma apm_b97a03_beta_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective (apm_b97a03_beta α) := by
  have ha : α ^ 2 ≠ 0 := pow_ne_zero _ (by
    intro ha
    have hpow := apm_b97a03_root_pow_six hα
    rw [ha] at hpow
    norm_num at hpow)
  intro i j hij
  apply Fin.ext
  have hpow := (apm_b97a03_zeta_primitive hα).pow_inj
    (show 2 * (i : ℕ) < 6 by omega) (show 2 * (j : ℕ) < 6 by omega)
    (mul_right_cancel₀ ha (by simpa [apm_b97a03_beta] using hij))
  omega

lemma apm_b97a03_beta_minpoly {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 3) : minpoly ℚ (apm_b97a03_beta α k) = apm_b97a03_cubic := by
  symm
  apply minpoly.eq_of_irreducible_of_monic apm_b97a03_cubic_irreducible
  · simpa [Polynomial.IsRoot, Polynomial.aeval_def] using apm_b97a03_beta_root hα k
  · exact Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 3 ≠ 0)

lemma apm_b97a03_beta_finrank {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 3) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {apm_b97a03_beta α k}) = 3 := by
  have hint : IsIntegral ℚ (apm_b97a03_beta α k) := by
    refine ⟨apm_b97a03_cubic,
      Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 3 ≠ 0), ?_⟩
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using apm_b97a03_beta_root hα k
  rw [IntermediateField.adjoin.finrank hint, apm_b97a03_beta_minpoly hα k]
  exact Polynomial.natDegree_X_pow_add_C

lemma apm_b97a03_zeta_sq_primitive {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IsPrimitiveRoot (apm_b97a03_zeta α ^ 2) 3 := by
  exact (apm_b97a03_zeta_primitive hα).pow (by norm_num) (by norm_num)

lemma apm_b97a03_cubic_root_exhaustion {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    ∀ z : ℂ, (apm_b97a03_cubic.map (algebraMap ℚ ℂ)).IsRoot z →
      ∃ k : Fin 3, z = apm_b97a03_beta α k := by
  intro z hz
  have hcube : (α ^ 2) ^ 3 = (-3 : ℂ) := by
    rw [← pow_mul, show 2 * 3 = 6 by norm_num]
    exact apm_b97a03_root_pow_six hα
  have hfac := X_pow_sub_C_eq_prod (apm_b97a03_zeta_sq_primitive hα)
    (by norm_num : 0 < 3) hcube
  have hz' : (Polynomial.X ^ 3 - Polynomial.C (-3 : ℂ)).IsRoot z := by
    simpa [apm_b97a03_cubic, Polynomial.IsRoot] using hz
  rw [hfac] at hz'
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, Finset.prod_eq_zero_iff] at hz'
  obtain ⟨k, hk, heq⟩ := hz'
  refine ⟨⟨k, by simpa using hk⟩, ?_⟩
  simpa [apm_b97a03_beta, pow_mul] using heq

lemma apm_b97a03_beta_zero (α : ℂ) : apm_b97a03_beta α 0 = α ^ 2 := by
  simp [apm_b97a03_beta]

lemma apm_b97a03_beta_one (α : ℂ) :
    apm_b97a03_beta α 1 = apm_b97a03_zeta α ^ 2 * α ^ 2 := by
  simp [apm_b97a03_beta]

lemma apm_b97a03_beta_mem_field (α : ℂ) (k : Fin 3) :
    apm_b97a03_beta α k ∈ apm_b97a03_field α := by
  rw [apm_b97a03_beta]
  exact IntermediateField.mul_mem _
    ((apm_b97a03_field α).toSubalgebra.pow_mem
      (apm_b97a03_zeta_mem_field (α := α)) _)
    ((apm_b97a03_field α).toSubalgebra.pow_mem
      (IntermediateField.subset_adjoin ℚ {α} (by simp)) 2)

noncomputable def apm_b97a03_betaField (α : ℂ) (k : Fin 3) :
    apm_b97a03_field α :=
  ⟨apm_b97a03_beta α k, apm_b97a03_beta_mem_field α k⟩

lemma apm_b97a03_betaField_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective (apm_b97a03_betaField α) := by
  intro i j hij
  apply apm_b97a03_beta_injective hα
  exact congrArg Subtype.val hij

lemma apm_b97a03_betaField_root {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : Fin 3) :
    (apm_b97a03_cubic.map
      (algebraMap ℚ (apm_b97a03_field α))).IsRoot
        (apm_b97a03_betaField α k) := by
  apply (Polynomial.isRoot_map_iff (apm_b97a03_field α).val.injective).mp
  simpa only [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ
    (apm_b97a03_field α) ℂ] using apm_b97a03_beta_root hα k

noncomputable def apm_b97a03_betaRoot {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 3) : apm_b97a03_cubic.rootSet (apm_b97a03_field α) := by
  refine ⟨apm_b97a03_betaField α k, ?_⟩
  rw [Polynomial.mem_rootSet']
  exact ⟨by
    simpa [apm_b97a03_cubic] using
      (Polynomial.monic_X_pow_add_C (3 : apm_b97a03_field α)
        (by norm_num : 3 ≠ 0)).ne_zero, by
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using
      apm_b97a03_betaField_root hα k⟩

lemma apm_b97a03_betaRoot_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective (apm_b97a03_betaRoot hα) := by
  intro i j hij
  apply apm_b97a03_betaField_injective hα
  exact congrArg Subtype.val hij

lemma apm_b97a03_betaRoot_surjective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Surjective (apm_b97a03_betaRoot hα) := by
  intro y
  have hyF : (apm_b97a03_cubic.map
      (algebraMap ℚ (apm_b97a03_field α))).IsRoot y.1 := by
    simpa [Polynomial.IsRoot, Polynomial.aeval_def] using
      (Polynomial.mem_rootSet'.mp y.2).2
  have hyC : (apm_b97a03_cubic.map (algebraMap ℚ ℂ)).IsRoot (y.1 : ℂ) := by
    have hm : ((apm_b97a03_cubic.map
        (algebraMap ℚ (apm_b97a03_field α))).map
          (apm_b97a03_field α).val).IsRoot ((apm_b97a03_field α).val y.1) :=
      hyF.map
    simpa only [Polynomial.map_map, IsScalarTower.algebraMap_eq ℚ
      (apm_b97a03_field α) ℂ] using hm
  obtain ⟨k, hk⟩ := apm_b97a03_cubic_root_exhaustion hα (y.1 : ℂ) hyC
  refine ⟨k, Subtype.ext ?_⟩
  apply Subtype.ext
  simpa [apm_b97a03_betaRoot, apm_b97a03_betaField] using hk.symm

noncomputable def apm_b97a03_betaRootEquiv {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Fin 3 ≃ apm_b97a03_cubic.rootSet (apm_b97a03_field α) :=
  Equiv.ofBijective (apm_b97a03_betaRoot hα)
    ⟨apm_b97a03_betaRoot_injective hα, apm_b97a03_betaRoot_surjective hα⟩

noncomputable def apm_b97a03_betaActionHom {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) →*
      Equiv.Perm (Fin 3) :=
  (apm_b97a03_betaRootEquiv hα).symm.permCongrHom.toMonoidHom.comp
    (MulAction.toPermHom
      (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α)
      (apm_b97a03_cubic.rootSet (apm_b97a03_field α)))

set_option synthInstance.maxHeartbeats 100000 in
lemma apm_b97a03_betaActionHom_apply {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) (k : Fin 3) :
    apm_b97a03_betaRoot hα (apm_b97a03_betaActionHom hα σ k) =
      σ • apm_b97a03_betaRoot hα k := by
  simp [apm_b97a03_betaActionHom, Equiv.permCongr_apply,
    apm_b97a03_betaRootEquiv]
  exact (apm_b97a03_betaRootEquiv hα).apply_symm_apply _

/-- Two cubic conjugates already recover the original sixth root. -/
lemma apm_b97a03_alpha_from_beta {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    α = (2 * (apm_b97a03_beta α 1 / apm_b97a03_beta α 0) + 1) /
      apm_b97a03_beta α 0 := by
  have ha : α ≠ 0 := by
    intro ha
    have hpow := apm_b97a03_root_pow_six hα
    rw [ha] at hpow
    norm_num at hpow
  have hrel := apm_b97a03_zeta_relation hα
  rw [apm_b97a03_beta_zero, apm_b97a03_beta_one]
  have hα3 : α ^ 3 = 2 * apm_b97a03_zeta α - 1 := by
    simp [apm_b97a03_zeta]
    ring
  have hzid : α ^ 3 = 2 * apm_b97a03_zeta α ^ 2 + 1 := by
    linear_combination hα3 - 2 * hrel
  field_simp [ha]
  exact hzid

lemma apm_b97a03_adjoin_two_beta {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IntermediateField.adjoin ℚ {apm_b97a03_beta α 0, apm_b97a03_beta α 1} =
      apm_b97a03_field α := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · rw [apm_b97a03_beta_zero]
      exact IntermediateField.pow_mem _
        (IntermediateField.subset_adjoin ℚ {α} (by simp)) 2
    · rw [apm_b97a03_beta_one]
      exact IntermediateField.mul_mem _
        (IntermediateField.pow_mem _ apm_b97a03_zeta_mem_field 2)
        (IntermediateField.pow_mem _
          (IntermediateField.subset_adjoin ℚ {α} (by simp)) 2)
  · rw [apm_b97a03_field, IntermediateField.adjoin_le_iff]
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    let S := IntermediateField.adjoin ℚ
      {apm_b97a03_beta α 0, apm_b97a03_beta α 1}
    have hb0 : apm_b97a03_beta α 0 ∈ S :=
      IntermediateField.subset_adjoin ℚ _ (by simp)
    have hb1 : apm_b97a03_beta α 1 ∈ S :=
      IntermediateField.subset_adjoin ℚ _ (by simp)
    have hrhs : (2 * (apm_b97a03_beta α 1 / apm_b97a03_beta α 0) + 1) /
        apm_b97a03_beta α 0 ∈ S := by
      apply IntermediateField.div_mem
      · exact IntermediateField.add_mem _
          (IntermediateField.mul_mem _ (IntermediateField.natCast_mem _ 2)
            (IntermediateField.div_mem _ hb1 hb0))
          (IntermediateField.one_mem _)
      · exact hb0
    change α ∈ S
    exact (apm_b97a03_alpha_from_beta hα).symm ▸ hrhs

lemma apm_b97a03_betaActionHom_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective (apm_b97a03_betaActionHom hα) := by
  intro σ τ hστ
  have hhom : σ.toAlgHom = τ.toAlgHom := by
    apply IntermediateField.algHom_ext_of_eq_adjoin ℚ
      (apm_b97a03_adjoin_two_beta hα).symm
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · have hk := Equiv.Perm.congr_fun hστ (0 : Fin 3)
      have hk' := congrArg (apm_b97a03_betaRoot hα) hk
      rw [apm_b97a03_betaActionHom_apply, apm_b97a03_betaActionHom_apply] at hk'
      exact congrArg Subtype.val hk'
    · have hk := Equiv.Perm.congr_fun hστ (1 : Fin 3)
      have hk' := congrArg (apm_b97a03_betaRoot hα) hk
      rw [apm_b97a03_betaActionHom_apply, apm_b97a03_betaActionHom_apply] at hk'
      exact congrArg Subtype.val hk'
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun hhom x

noncomputable def apm_b97a03_autMulEquiv {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) ≃*
      Equiv.Perm (Fin 3) := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) := apm_b97a03_isGalois hα
  refine MulEquiv.ofBijective (apm_b97a03_betaActionHom hα)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨apm_b97a03_betaActionHom_injective hα, ?_⟩)
  rw [← Nat.card_eq_fintype_card, apm_b97a03_card_aut hα,
    Fintype.card_perm]
  norm_num

lemma apm_b97a03_aut_mulEquiv_nonempty {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Nonempty ((apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) ≃*
      Equiv.Perm (Fin 3)) :=
  ⟨apm_b97a03_autMulEquiv hα⟩

@[simp] lemma apm_b97a03_autMulEquiv_apply {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) :
    apm_b97a03_autMulEquiv hα σ = apm_b97a03_betaActionHom hα σ := rfl

lemma apm_b97a03_adjoin_beta_zero (α : ℂ) :
    IntermediateField.adjoin ℚ {apm_b97a03_beta α 0} =
      IntermediateField.adjoin ℚ {α ^ 2} := by
  rw [apm_b97a03_beta_zero]

lemma apm_b97a03_adjoin_beta_one (α : ℂ) :
    IntermediateField.adjoin ℚ {apm_b97a03_beta α 1} =
      IntermediateField.adjoin ℚ {apm_b97a03_zeta α ^ 2 * α ^ 2} := by
  rw [apm_b97a03_beta_one]

lemma apm_b97a03_adjoin_beta_two (α : ℂ) :
    IntermediateField.adjoin ℚ {apm_b97a03_beta α 2} =
      IntermediateField.adjoin ℚ {apm_b97a03_zeta α ^ 4 * α ^ 2} := by
  simp [apm_b97a03_beta]

noncomputable def apm_b97a03_betaStabilizer {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 3) : Subgroup (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) :=
  Subgroup.comap (apm_b97a03_autMulEquiv hα).toMonoidHom
    (MulAction.stabilizer (Equiv.Perm (Fin 3)) k)

lemma apm_b97a03_betaStabilizer_eq_fixingSubgroup {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 3) :
    apm_b97a03_betaStabilizer hα k =
      (IntermediateField.adjoin ℚ {apm_b97a03_betaField α k}).fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  simp only [apm_b97a03_betaStabilizer, Subgroup.mem_comap,
    MulAction.mem_stabilizer_iff]
  constructor
  · intro hk x hx
    change apm_b97a03_betaActionHom hα σ k = k at hk
    have hgen : σ (apm_b97a03_betaField α k) = apm_b97a03_betaField α k := by
      have hr := apm_b97a03_betaActionHom_apply hα σ k
      rw [hk] at hr
      exact congrArg Subtype.val hr.symm
    refine IntermediateField.adjoin_induction ℚ (p := fun x _ => σ x = x) ?_ ?_ ?_ ?_ ?_ hx
    · intro y hy
      simpa only [Set.mem_singleton_iff] using hy ▸ hgen
    · intro q
      exact σ.commutes q
    · intro y z _ _ hy hz
      simp [hy, hz]
    · intro y _ hy
      simp [hy]
    · intro y z _ _ hy hz
      simp [hy, hz]
  · intro hfix
    change apm_b97a03_betaActionHom hα σ k = k
    apply apm_b97a03_betaRoot_injective hα
    rw [apm_b97a03_betaActionHom_apply]
    apply Subtype.ext
    apply Subtype.ext
    simpa [apm_b97a03_betaRoot, apm_b97a03_betaField] using congrArg Subtype.val
      (hfix (apm_b97a03_betaField α k)
        (IntermediateField.subset_adjoin ℚ _ (by simp)))

lemma apm_b97a03_fixedField_betaStabilizer {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 3) :
    IntermediateField.fixedField (apm_b97a03_betaStabilizer hα k) =
      IntermediateField.adjoin ℚ {apm_b97a03_betaField α k} := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) := apm_b97a03_isGalois hα
  rw [apm_b97a03_betaStabilizer_eq_fixingSubgroup hα k,
    IsGalois.fixedField_fixingSubgroup]

lemma apm_b97a03_alpha_three_from_beta_ratio {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    α ^ 3 = 2 * (apm_b97a03_beta α 1 / apm_b97a03_beta α 0) + 1 := by
  have ha : α ≠ 0 := by
    intro ha
    have hpow := apm_b97a03_root_pow_six hα
    rw [ha] at hpow
    norm_num at hpow
  have hrel := apm_b97a03_zeta_relation hα
  rw [apm_b97a03_beta_zero, apm_b97a03_beta_one]
  have hα3 : α ^ 3 = 2 * apm_b97a03_zeta α - 1 := by
    simp [apm_b97a03_zeta]
    ring
  have hzid : α ^ 3 = 2 * apm_b97a03_zeta α ^ 2 + 1 := by
    linear_combination hα3 - 2 * hrel
  field_simp [ha]
  exact hzid

noncomputable def apm_b97a03_quadratic : ℚ[X] :=
  Polynomial.X ^ 2 + Polynomial.C 3

lemma apm_b97a03_quadratic_irreducible :
    Irreducible apm_b97a03_quadratic := by
  rw [show apm_b97a03_quadratic = Polynomial.X ^ 2 - Polynomial.C (-3 : ℚ) by
    simp [apm_b97a03_quadratic]]
  apply X_pow_sub_C_irreducible_of_prime (by norm_num)
  intro b hb
  have hs : 0 ≤ b ^ 2 := sq_nonneg b
  linarith

lemma apm_b97a03_alpha_three_minpoly {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    minpoly ℚ (α ^ 3) = apm_b97a03_quadratic := by
  symm
  apply minpoly.eq_of_irreducible_of_monic apm_b97a03_quadratic_irreducible
  · have hs := apm_b97a03_root_pow_three_sq hα
    simpa [apm_b97a03_quadratic, Polynomial.aeval_def] using
      (show (α ^ 3) ^ 2 + 3 = 0 by linear_combination hs)
  · exact Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 2 ≠ 0)

lemma apm_b97a03_alpha_three_finrank {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ {α ^ 3}) = 2 := by
  have hint : IsIntegral ℚ (α ^ 3) := by
    refine ⟨apm_b97a03_quadratic,
      Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 2 ≠ 0), ?_⟩
    have hs := apm_b97a03_root_pow_three_sq hα
    simpa [apm_b97a03_quadratic, Polynomial.aeval_def] using
      (show (α ^ 3) ^ 2 + 3 = 0 by linear_combination hs)
  rw [IntermediateField.adjoin.finrank hint, apm_b97a03_alpha_three_minpoly hα]
  exact Polynomial.natDegree_X_pow_add_C

lemma apm_b97a03_alpha_three_from_beta_ratio_one {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    α ^ 3 = 2 * (apm_b97a03_beta α 2 / apm_b97a03_beta α 1) + 1 := by
  have ha : α ≠ 0 := by
    intro ha
    have := apm_b97a03_root_pow_six hα
    simp [ha] at this
  rw [apm_b97a03_alpha_three_from_beta_ratio hα]
  have hz6 := apm_b97a03_zeta_pow_six hα
  simp [apm_b97a03_beta]
  field_simp [ha]

lemma apm_b97a03_alpha_three_from_beta_ratio_two {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    α ^ 3 = 2 * (apm_b97a03_beta α 0 / apm_b97a03_beta α 2) + 1 := by
  have ha : α ≠ 0 := by
    intro ha
    have := apm_b97a03_root_pow_six hα
    simp [ha] at this
  rw [apm_b97a03_alpha_three_from_beta_ratio hα]
  have hz6 := apm_b97a03_zeta_pow_six hα
  have hz : apm_b97a03_zeta α ≠ 0 := by
    intro h
    simp [h] at hz6
  simp [apm_b97a03_beta]
  field_simp [ha, hz]
  ring_nf at hz6 ⊢
  exact hz6

noncomputable def apm_b97a03_alphaThreeField (α : ℂ) :
    apm_b97a03_field α :=
  ⟨α ^ 3, IntermediateField.pow_mem _
    (IntermediateField.subset_adjoin ℚ {α} (by simp)) 3⟩

lemma apm_b97a03_alphaThreeField_ratio {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_alphaThreeField α =
      2 * (apm_b97a03_betaField α 1 / apm_b97a03_betaField α 0) + 1 := by
  apply Subtype.ext
  exact apm_b97a03_alpha_three_from_beta_ratio hα

lemma apm_b97a03_alphaThreeField_ratio_one {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_alphaThreeField α =
      2 * (apm_b97a03_betaField α 2 / apm_b97a03_betaField α 1) + 1 := by
  apply Subtype.ext
  exact apm_b97a03_alpha_three_from_beta_ratio_one hα

lemma apm_b97a03_alphaThreeField_ratio_two {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_alphaThreeField α =
      2 * (apm_b97a03_betaField α 0 / apm_b97a03_betaField α 2) + 1 := by
  apply Subtype.ext
  exact apm_b97a03_alpha_three_from_beta_ratio_two hα

lemma apm_b97a03_aut_betaField {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) (k : Fin 3) :
    σ (apm_b97a03_betaField α k) =
      apm_b97a03_betaField α (apm_b97a03_betaActionHom hα σ k) := by
  have h := apm_b97a03_betaActionHom_apply hα σ k
  exact congrArg (fun x : apm_b97a03_cubic.rootSet (apm_b97a03_field α) =>
    (x : apm_b97a03_field α)) h.symm

noncomputable def apm_b97a03_internalField {α : ℂ}
    (L : IntermediateField ℚ ℂ) : IntermediateField ℚ (apm_b97a03_field α) :=
  IntermediateField.comap (apm_b97a03_field α).val L

lemma apm_b97a03_internalField_map {α : ℂ} (L : IntermediateField ℚ ℂ)
    (hL : L ≤ apm_b97a03_field α) :
    IntermediateField.map (apm_b97a03_field α).val
      (apm_b97a03_internalField L) = L := by
  apply IntermediateField.map_comap_eq_self
  simpa only [IntermediateField.fieldRange_val] using hL

lemma apm_b97a03_internalField_eq_iff {α : ℂ}
    {L M : IntermediateField ℚ ℂ} (hL : L ≤ apm_b97a03_field α)
    (hM : M ≤ apm_b97a03_field α) :
    apm_b97a03_internalField (α := α) L =
      apm_b97a03_internalField (α := α) M ↔ L = M := by
  constructor
  · intro h
    have hm := congrArg (IntermediateField.map (apm_b97a03_field α).val) h
    simpa [apm_b97a03_internalField_map L hL,
      apm_b97a03_internalField_map M hM] using hm
  · exact fun h => congrArg (apm_b97a03_internalField (α := α)) h

abbrev apm_b97a03_swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
abbrev apm_b97a03_swap02 : Equiv.Perm (Fin 3) := Equiv.swap 0 2
abbrev apm_b97a03_swap12 : Equiv.Perm (Fin 3) := Equiv.swap 1 2
abbrev apm_b97a03_cycle012 : Equiv.Perm (Fin 3) :=
  apm_b97a03_swap01 * apm_b97a03_swap12

/-- A computationally verified normal form for permutations of three points.
This is the executable core used by the symbolic subgroup census. -/
lemma apm_b97a03_perm3_cases (σ : Equiv.Perm (Fin 3)) :
    σ = 1 ∨ σ = apm_b97a03_swap01 ∨ σ = apm_b97a03_swap02 ∨
      σ = apm_b97a03_swap12 ∨ σ = apm_b97a03_cycle012 ∨
      σ = apm_b97a03_cycle012 ^ 2 := by
  decide +revert

lemma apm_b97a03_perm3_nontrivial_distinct :
    apm_b97a03_swap01 ≠ 1 ∧ apm_b97a03_swap02 ≠ 1 ∧
      apm_b97a03_swap12 ≠ 1 ∧ apm_b97a03_cycle012 ≠ 1 ∧
      apm_b97a03_cycle012 ^ 2 ≠ 1 := by
  decide

lemma apm_b97a03_perm3_cycle_mul_cycle :
    apm_b97a03_cycle012 * apm_b97a03_cycle012 =
      apm_b97a03_cycle012 ^ 2 ∧
    apm_b97a03_cycle012 * apm_b97a03_cycle012 ^ 2 = 1 := by
  decide

lemma apm_b97a03_mem_alternating3_iff (σ : Equiv.Perm (Fin 3)) :
    σ ∈ alternatingGroup (Fin 3) ↔
      σ = 1 ∨ σ = apm_b97a03_cycle012 ∨
        σ = apm_b97a03_cycle012 ^ 2 := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +revert

lemma apm_b97a03_alternating3_elements :
    (alternatingGroup (Fin 3) : Set (Equiv.Perm (Fin 3))) =
      {1, apm_b97a03_cycle012, apm_b97a03_cycle012 ^ 2} := by
  ext σ
  exact apm_b97a03_mem_alternating3_iff σ

lemma apm_b97a03_alternating_fixes_alphaThree {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α)
    (hσ : apm_b97a03_autMulEquiv hα σ ∈ alternatingGroup (Fin 3)) :
    σ (apm_b97a03_alphaThreeField α) = apm_b97a03_alphaThreeField α := by
  rw [apm_b97a03_mem_alternating3_iff] at hσ
  rcases hσ with hσ | hσ | hσ
  · have hs : σ = 1 := (apm_b97a03_autMulEquiv hα).injective (by simpa using hσ)
    simp [hs]
  · have h0 : apm_b97a03_betaActionHom hα σ 0 = 1 := by
      rw [← apm_b97a03_autMulEquiv_apply, hσ]
      decide
    have h1 : apm_b97a03_betaActionHom hα σ 1 = 2 := by
      rw [← apm_b97a03_autMulEquiv_apply, hσ]
      decide
    rw [apm_b97a03_alphaThreeField_ratio hα]
    simp only [map_add, map_mul, map_div₀, map_ofNat, map_one]
    rw [apm_b97a03_aut_betaField hα σ 0,
      apm_b97a03_aut_betaField hα σ 1, h0, h1]
    exact (apm_b97a03_alphaThreeField_ratio_one hα).symm.trans
      (apm_b97a03_alphaThreeField_ratio hα)
  · have h0 : apm_b97a03_betaActionHom hα σ 0 = 2 := by
      rw [← apm_b97a03_autMulEquiv_apply, hσ]
      decide
    have h1 : apm_b97a03_betaActionHom hα σ 1 = 0 := by
      rw [← apm_b97a03_autMulEquiv_apply, hσ]
      decide
    rw [apm_b97a03_alphaThreeField_ratio hα]
    simp only [map_add, map_mul, map_div₀, map_ofNat, map_one]
    rw [apm_b97a03_aut_betaField hα σ 0,
      apm_b97a03_aut_betaField hα σ 1, h0, h1]
    exact (apm_b97a03_alphaThreeField_ratio_two hα).symm.trans
      (apm_b97a03_alphaThreeField_ratio hα)

noncomputable def apm_b97a03_alternatingPreimage {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Subgroup (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) :=
  Subgroup.comap (apm_b97a03_autMulEquiv hα).toMonoidHom
    (alternatingGroup (Fin 3))

lemma apm_b97a03_alphaThree_mem_fixedField {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_alphaThreeField α ∈
      IntermediateField.fixedField (apm_b97a03_alternatingPreimage hα) := by
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  exact apm_b97a03_alternating_fixes_alphaThree hα σ hσ

lemma apm_b97a03_adjoin_alphaThree_le_fixedField {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IntermediateField.adjoin ℚ {apm_b97a03_alphaThreeField α} ≤
      IntermediateField.fixedField (apm_b97a03_alternatingPreimage hα) := by
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simpa only [Set.mem_singleton_iff] using
    hx ▸ apm_b97a03_alphaThree_mem_fixedField hα

noncomputable def apm_b97a03_alternatingPreimageEquiv {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_alternatingPreimage hα ≃ alternatingGroup (Fin 3) where
  toFun σ := ⟨apm_b97a03_autMulEquiv hα σ, σ.property⟩
  invFun τ := ⟨(apm_b97a03_autMulEquiv hα).symm τ, by
    change apm_b97a03_autMulEquiv hα
      ((apm_b97a03_autMulEquiv hα).symm τ) ∈ alternatingGroup (Fin 3)
    rw [MulEquiv.apply_symm_apply]
    exact τ.property⟩
  left_inv σ := Subtype.ext ((apm_b97a03_autMulEquiv hα).symm_apply_apply σ)
  right_inv τ := Subtype.ext ((apm_b97a03_autMulEquiv hα).apply_symm_apply τ)

set_option maxHeartbeats 500000 in
lemma apm_b97a03_card_alternatingPreimage {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Nat.card (apm_b97a03_alternatingPreimage hα) = 3 := by
  rw [Nat.card_congr (apm_b97a03_alternatingPreimageEquiv hα),
    nat_card_alternatingGroup]
  norm_num

set_option maxHeartbeats 500000 in
lemma apm_b97a03_finrank_fixedField_alternating {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ
      (IntermediateField.fixedField (apm_b97a03_alternatingPreimage hα)) = 2 := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  let K := IntermediateField.fixedField (apm_b97a03_alternatingPreimage hα)
  have htower := Module.finrank_mul_finrank ℚ K (apm_b97a03_field α)
  have hrelative : Module.finrank K (apm_b97a03_field α) = 3 := by
    rw [IntermediateField.finrank_fixedField_eq_card,
      apm_b97a03_card_alternatingPreimage hα]
  rw [hrelative, apm_b97a03_finrank hα] at htower
  change Module.finrank ℚ K = 2
  omega

lemma apm_b97a03_fixedField_alternating {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IntermediateField.fixedField (apm_b97a03_alternatingPreimage hα) =
      IntermediateField.adjoin ℚ {apm_b97a03_alphaThreeField α} := by
  symm
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  apply IntermediateField.eq_of_le_of_finrank_eq
    (apm_b97a03_adjoin_alphaThree_le_fixedField hα)
  rw [apm_b97a03_finrank_fixedField_alternating hα]
  have hint : IsIntegral ℚ (apm_b97a03_alphaThreeField α) := by
    refine ⟨apm_b97a03_quadratic,
      Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 2 ≠ 0), by
        apply Subtype.ext
        have hs := apm_b97a03_root_pow_three_sq hα
        simpa [apm_b97a03_quadratic, Polynomial.aeval_def,
          apm_b97a03_alphaThreeField] using
          (show (α ^ 3) ^ 2 + 3 = 0 by linear_combination hs)⟩
  rw [IntermediateField.adjoin.finrank hint]
  have hmin : minpoly ℚ (apm_b97a03_alphaThreeField α) =
      apm_b97a03_quadratic := by
    symm
    apply minpoly.eq_of_irreducible_of_monic apm_b97a03_quadratic_irreducible
    · apply Subtype.ext
      have hs := apm_b97a03_root_pow_three_sq hα
      simpa [apm_b97a03_quadratic, Polynomial.aeval_def,
        apm_b97a03_alphaThreeField] using
        (show (α ^ 3) ^ 2 + 3 = 0 by linear_combination hs)
    · exact Polynomial.monic_X_pow_add_C (3 : ℚ) (by norm_num : 2 ≠ 0)
  rw [hmin]
  exact Polynomial.natDegree_X_pow_add_C

lemma apm_b97a03_perm3_mul_table :
    apm_b97a03_cycle012 * apm_b97a03_swap01 = apm_b97a03_swap02 ∧
    apm_b97a03_cycle012 ^ 2 * apm_b97a03_swap01 = apm_b97a03_swap12 ∧
    apm_b97a03_cycle012 * apm_b97a03_swap02 = apm_b97a03_swap12 ∧
    apm_b97a03_cycle012 ^ 2 * apm_b97a03_swap02 = apm_b97a03_swap01 ∧
    apm_b97a03_cycle012 * apm_b97a03_swap12 = apm_b97a03_swap01 ∧
    apm_b97a03_cycle012 ^ 2 * apm_b97a03_swap12 = apm_b97a03_swap02 ∧
    apm_b97a03_swap01 * apm_b97a03_swap02 = apm_b97a03_cycle012 ^ 2 ∧
    apm_b97a03_swap01 * apm_b97a03_swap12 = apm_b97a03_cycle012 ∧
    apm_b97a03_swap02 * apm_b97a03_swap12 = apm_b97a03_cycle012 ^ 2 ∧
    apm_b97a03_cycle012 ^ 2 * apm_b97a03_cycle012 ^ 2 =
      apm_b97a03_cycle012 := by
  decide

lemma apm_b97a03_mem_stabilizer0_iff (σ : Equiv.Perm (Fin 3)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3) ↔
      σ = 1 ∨ σ = apm_b97a03_swap12 := by
  rw [MulAction.mem_stabilizer_iff]
  decide +revert

lemma apm_b97a03_mem_stabilizer1_iff (σ : Equiv.Perm (Fin 3)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) (1 : Fin 3) ↔
      σ = 1 ∨ σ = apm_b97a03_swap02 := by
  rw [MulAction.mem_stabilizer_iff]
  decide +revert

lemma apm_b97a03_mem_stabilizer2_iff (σ : Equiv.Perm (Fin 3)) :
    σ ∈ MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3) ↔
      σ = 1 ∨ σ = apm_b97a03_swap01 := by
  rw [MulAction.mem_stabilizer_iff]
  decide +revert

/-- The six subgroups of `S₃`, presented in the form needed by the Galois
correspondence below. -/
lemma apm_b97a03_subgroup_perm3_cases (H : Subgroup (Equiv.Perm (Fin 3))) :
    H = ⊥ ∨
    H = MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3) ∨
    H = MulAction.stabilizer (Equiv.Perm (Fin 3)) (1 : Fin 3) ∨
    H = MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3) ∨
    H = alternatingGroup (Fin 3) ∨ H = ⊤ := by
  rcases apm_b97a03_perm3_mul_table with
    ⟨hc01, hc201, hc02, hc202, hc12, hc212, h0102, h0112, h0212, hc2c2⟩
  by_cases hc : apm_b97a03_cycle012 ∈ H
  · have hc2 : apm_b97a03_cycle012 ^ 2 ∈ H := by
      simpa [pow_two] using H.mul_mem hc hc
    by_cases h01 : apm_b97a03_swap01 ∈ H
    · right; right; right; right; right
      have h02 : apm_b97a03_swap02 ∈ H := hc01 ▸ H.mul_mem hc h01
      have h12 : apm_b97a03_swap12 ∈ H := hc201 ▸ H.mul_mem hc2 h01
      ext σ
      constructor
      · exact fun _ => trivial
      · intro _
        rcases apm_b97a03_perm3_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
        · exact H.one_mem
        · exact h01
        · exact h02
        · exact h12
        · exact hc
        · exact hc2
    · by_cases h02 : apm_b97a03_swap02 ∈ H
      · right; right; right; right; right
        have h12 : apm_b97a03_swap12 ∈ H := hc02 ▸ H.mul_mem hc h02
        have h01' : apm_b97a03_swap01 ∈ H := hc202 ▸ H.mul_mem hc2 h02
        exact (h01 h01').elim
      · by_cases h12 : apm_b97a03_swap12 ∈ H
        · right; right; right; right; right
          have h01' : apm_b97a03_swap01 ∈ H := hc12 ▸ H.mul_mem hc h12
          exact (h01 h01').elim
        · right; right; right; right; left
          ext σ
          rw [apm_b97a03_mem_alternating3_iff]
          constructor
          · intro hσ
            rcases apm_b97a03_perm3_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact (h01 hσ).elim
            · exact (h02 hσ).elim
            · exact (h12 hσ).elim
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr rfl)
          · rintro (rfl | rfl | rfl)
            · exact H.one_mem
            · exact hc
            · exact hc2
  · have hc2 : apm_b97a03_cycle012 ^ 2 ∉ H := by
      intro h
      exact hc (hc2c2 ▸ H.mul_mem h h)
    by_cases h01 : apm_b97a03_swap01 ∈ H
    · by_cases h02 : apm_b97a03_swap02 ∈ H
      · exact (hc2 (h0102 ▸ H.mul_mem h01 h02)).elim
      · by_cases h12 : apm_b97a03_swap12 ∈ H
        · exact (hc (h0112 ▸ H.mul_mem h01 h12)).elim
        · right; right; right; left
          ext σ
          rw [apm_b97a03_mem_stabilizer2_iff]
          constructor
          · intro hσ
            rcases apm_b97a03_perm3_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact (h02 hσ).elim
            · exact (h12 hσ).elim
            · exact (hc hσ).elim
            · exact (hc2 hσ).elim
          · rintro (rfl | rfl)
            · exact H.one_mem
            · exact h01
    · by_cases h02 : apm_b97a03_swap02 ∈ H
      · by_cases h12 : apm_b97a03_swap12 ∈ H
        · exact (hc2 (h0212 ▸ H.mul_mem h02 h12)).elim
        · right; right; left
          ext σ
          rw [apm_b97a03_mem_stabilizer1_iff]
          constructor
          · intro hσ
            rcases apm_b97a03_perm3_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact (h01 hσ).elim
            · exact Or.inr rfl
            · exact (h12 hσ).elim
            · exact (hc hσ).elim
            · exact (hc2 hσ).elim
          · rintro (rfl | rfl)
            · exact H.one_mem
            · exact h02
      · by_cases h12 : apm_b97a03_swap12 ∈ H
        · right; left
          ext σ
          rw [apm_b97a03_mem_stabilizer0_iff]
          constructor
          · intro hσ
            rcases apm_b97a03_perm3_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact (h01 hσ).elim
            · exact (h02 hσ).elim
            · exact Or.inr rfl
            · exact (hc hσ).elim
            · exact (hc2 hσ).elim
          · rintro (rfl | rfl)
            · exact H.one_mem
            · exact h12
        · left
          ext σ
          constructor
          · intro hσ
            rcases apm_b97a03_perm3_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
            · simp
            · exact (h01 hσ).elim
            · exact (h02 hσ).elim
            · exact (h12 hσ).elim
            · exact (hc hσ).elim
            · exact (hc2 hσ).elim
          · intro hσ
            have : σ = 1 := by simpa using hσ
            subst σ
            exact H.one_mem

set_option maxHeartbeats 500000 in
lemma apm_b97a03_internalField_cases {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (K : IntermediateField ℚ (apm_b97a03_field α)) :
    K = ⊥ ∨
    K = IntermediateField.adjoin ℚ {apm_b97a03_alphaThreeField α} ∨
    K = IntermediateField.adjoin ℚ {apm_b97a03_betaField α 0} ∨
    K = IntermediateField.adjoin ℚ {apm_b97a03_betaField α 1} ∨
    K = IntermediateField.adjoin ℚ {apm_b97a03_betaField α 2} ∨ K = ⊤ := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) := apm_b97a03_isGalois hα
  let φ := (apm_b97a03_autMulEquiv hα).toMonoidHom
  let H := K.fixingSubgroup
  let S := Subgroup.map φ H
  have hpull : Subgroup.comap φ S = H :=
    Subgroup.comap_map_eq_self_of_injective
      (apm_b97a03_autMulEquiv hα).injective H
  have hK : K = IntermediateField.fixedField H :=
    (IsGalois.fixedField_fixingSubgroup K).symm
  rcases apm_b97a03_subgroup_perm3_cases S with
    hS | hS | hS | hS | hS | hS
  · right; right; right; right; right
    rw [hK, ← hpull, hS]
    have hker : φ.ker = ⊥ :=
      φ.ker_eq_bot_iff.mpr (apm_b97a03_autMulEquiv hα).injective
    change IntermediateField.fixedField φ.ker = ⊤
    rw [hker, IntermediateField.fixedField_bot]
  · right; right; left
    rw [hK, ← hpull, hS]
    exact apm_b97a03_fixedField_betaStabilizer hα 0
  · right; right; right; left
    rw [hK, ← hpull, hS]
    exact apm_b97a03_fixedField_betaStabilizer hα 1
  · right; right; right; right; left
    rw [hK, ← hpull, hS]
    exact apm_b97a03_fixedField_betaStabilizer hα 2
  · right; left
    rw [hK, ← hpull, hS]
    exact apm_b97a03_fixedField_alternating hα
  · left
    rw [hK, ← hpull, hS]
    simp [φ]

/-- Why this unblocks `apm_b97a03`: it is the concrete Galois-theoretic
classification left after root exhaustion: the automorphism group is `S₃`
and the displayed six fields exhaust the intermediate-field lattice. -/
theorem apm_b97A03_bridge_3 {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Nonempty
        ((apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) ≃*
          Equiv.Perm (Fin 3)) ∧
      ∀ L : IntermediateField ℚ ℂ,
        L ≤ apm_b97a03_field α →
        L = ⊥ ∨
        L = IntermediateField.adjoin ℚ {α ^ 3} ∨
        L = IntermediateField.adjoin ℚ {α ^ 2} ∨
        L = IntermediateField.adjoin ℚ
          {(apm_b97a03_zeta α) ^ 2 * α ^ 2} ∨
        L = IntermediateField.adjoin ℚ
          {(apm_b97a03_zeta α) ^ 4 * α ^ 2} ∨
        L = apm_b97a03_field α := by
  refine ⟨apm_b97a03_aut_mulEquiv_nonempty hα, ?_⟩
  intro L hL
  rcases apm_b97a03_internalField_cases hα
      (apm_b97a03_internalField L) with hK | hK | hK | hK | hK | hK
  all_goals
    have hm := congrArg (IntermediateField.map (apm_b97a03_field α).val) hK
    rw [apm_b97a03_internalField_map L hL] at hm
  · left
    exact hm.trans (IntermediateField.map_bot _)
  · right; left
    calc
      L = IntermediateField.map (apm_b97a03_field α).val
          (IntermediateField.adjoin ℚ {apm_b97a03_alphaThreeField α}) := hm
      _ = IntermediateField.adjoin ℚ
          ((apm_b97a03_field α).val '' {apm_b97a03_alphaThreeField α}) :=
        IntermediateField.adjoin_map ℚ _ _
      _ = IntermediateField.adjoin ℚ {α ^ 3} := by
        simp [apm_b97a03_alphaThreeField]
        rfl
  · right; right; left
    calc
      L = IntermediateField.map (apm_b97a03_field α).val
          (IntermediateField.adjoin ℚ {apm_b97a03_betaField α 0}) := hm
      _ = IntermediateField.adjoin ℚ
          ((apm_b97a03_field α).val '' {apm_b97a03_betaField α 0}) :=
        IntermediateField.adjoin_map ℚ _ _
      _ = IntermediateField.adjoin ℚ {α ^ 2} := by
        simp [apm_b97a03_betaField, apm_b97a03_beta_zero]
  · right; right; right; left
    calc
      L = IntermediateField.map (apm_b97a03_field α).val
          (IntermediateField.adjoin ℚ {apm_b97a03_betaField α 1}) := hm
      _ = IntermediateField.adjoin ℚ
          ((apm_b97a03_field α).val '' {apm_b97a03_betaField α 1}) :=
        IntermediateField.adjoin_map ℚ _ _
      _ = IntermediateField.adjoin ℚ
          {apm_b97a03_zeta α ^ 2 * α ^ 2} := by
        simp [apm_b97a03_betaField, apm_b97a03_beta_one]
  · right; right; right; right; left
    calc
      L = IntermediateField.map (apm_b97a03_field α).val
          (IntermediateField.adjoin ℚ {apm_b97a03_betaField α 2}) := hm
      _ = IntermediateField.adjoin ℚ
          ((apm_b97a03_field α).val '' {apm_b97a03_betaField α 2}) :=
        IntermediateField.adjoin_map ℚ _ _
      _ = IntermediateField.adjoin ℚ
          {apm_b97a03_zeta α ^ 4 * α ^ 2} := by
        simp [apm_b97a03_betaField, apm_b97a03_beta]
  · right; right; right; right; right
    exact hm.trans ((AlgHom.fieldRange_eq_map _).symm.trans
      (IntermediateField.fieldRange_val (apm_b97a03_field α)))

theorem apm_b97a03 :
    Irreducible apm_b97a03_polynomial ∧
    ∀ α : ℂ,
      (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α →
      (∀ z : ℂ,
        (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot z →
          z ∈ apm_b97a03_field α) ∧
      Nonempty
        ((apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) ≃*
          Equiv.Perm (Fin 3)) ∧
      ∀ L : IntermediateField ℚ ℂ,
        L ≤ apm_b97a03_field α →
        L = ⊥ ∨
        L = IntermediateField.adjoin ℚ {α ^ 3} ∨
        L = IntermediateField.adjoin ℚ {α ^ 2} ∨
        L = IntermediateField.adjoin ℚ
          {(apm_b97a03_zeta α) ^ 2 * α ^ 2} ∨
        L = IntermediateField.adjoin ℚ
          {(apm_b97a03_zeta α) ^ 4 * α ^ 2} ∨
        L = apm_b97a03_field α := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib contains Eisenstein machinery
  (`Polynomial.IsEisensteinAt.irreducible`), splitting-field/adjoin lemmas such
  as `IsSplittingField.adjoin_rootSet`, and the abstract correspondence
  `IsGalois.intermediateFieldEquivSubgroup`. Local source and solved-sibling
  searches found no implementation of the concrete bridges required here:
  deriving all six complex roots from an arbitrary root `α`, proving the
  embedded field `adjoin ℚ {α}` is the splitting field, constructing its six
  automorphisms and the displayed `S₃` equivalence, and identifying the fixed
  fields of the four proper nontrivial subgroups with the exact listed adjoins.

  The abstract Galois correspondence alone does not establish completeness of
  this explicit embedded-field list; it additionally needs a classification of
  subgroups of `Equiv.Perm (Fin 3)` and degree/fixed-point calculations for each
  generator.

  Closer hop 1 closes the first radical/root-of-unity calculation in three
  compiled lemmas. `apm_b97a03_root_pow_six` extracts `α⁶ = -3` from the
  mapped-polynomial root hypothesis; `apm_b97a03_root_pow_three_sq` obtains
  `(α³)² = -3`; and `apm_b97a03_zeta_relation` proves that the statement's
  `ζ = (1 + α³)/2` satisfies `ζ² - ζ + 1 = 0`. Thus the sixth-root-of-unity
  ingredient is now constructed explicitly from `α`, inside the same adjoin.
  Renewed searches of `LEMMA-INDEX.md`, all closed artifacts,
  `ConstructionTargets/`, Kummer extensions, and splitting-field APIs found no
  packaged theorem converting this quadratic relation into the exact six-root
  list or the four displayed fixed fields. The statement appears
  mathematically sound, but the remaining concrete splitting-field,
  automorphism, subgroup, and fixed-field development remains open.

  Closer hop 2 pushes the explicit root construction further.
  `apm_b97a03_zeta_pow_three` and `apm_b97a03_zeta_pow_six` turn the
  quadratic relation into `ζ³ = -1` and `ζ⁶ = 1`.
  `apm_b97a03_zeta_mem_field` proves `ζ ∈ ℚ(α)`, while
  `apm_b97a03_zeta_mul_root` and `apm_b97a03_zeta_mul_root_mem_field` prove
  that every `ζ^k α` is a root lying in the same adjoin. This supplies the
  candidate six-root orbit without a Kummer API. Remaining are proving the
  six candidates exhaust the root set (including distinctness), packaging the
  splitting field and automorphisms, and computing the exact fixed fields.

  Closer hop 3 proves `apm_b97a03_zeta_primitive`, showing that the derived
  element has exact order six, and
  `apm_b97a03_candidate_roots_injective`, showing the six compiled candidates
  are pairwise distinct.  Together with hop 2, this gives six distinct roots
  of the degree-six polynomial inside `ℚ(α)`.  The remaining bridge is to turn
  that fact into root-set exhaustion/splitting in the exact API, then package
  the automorphisms and fixed-field classification.

  Solver hop 4 closes two independent obligations. `apm_b97A03_bridge_1` now
  proves irreducibility by applying Eisenstein at `(3)` to the integral lift
  `X⁶ + 3`, then transports the result to `ℚ[X]` with Gauss's lemma.
  `apm_b97a03_root_exhaustion` uses the primitive-root product formula to show
  directly that every complex root is one of the six candidates.  The
  splitting-field half of bridge 2 is now also packaged: uniqueness of the
  rational algebra structure transports the goal to the intermediate-field
  API, root exhaustion proves both splitting and the two adjoin inclusions.
  The final theorem is assembled from the bridges.  Only bridge 3 remains:
  construct the six automorphisms and their `S₃` equivalence, then use the
  Galois correspondence to calculate the five proper displayed fixed fields.

  Solver hop 5 builds the numerical Galois infrastructure at bridge 3's
  interface.  The minimal polynomial of `α` is now identified with `X⁶ + 3`,
  its integrality and the exact finrank `6` are compiled, the splitting-field
  result supplies an `IsGalois` instance, and `apm_b97a03_card_aut` proves that
  the automorphism group has exactly six elements.  What remains is structural,
  not cardinal: exhibit its noncommuting order-two/order-three generators (or
  its faithful action on the three cubic conjugates), then compute the fixed
  fields of the resulting six subgroups.

  Solver hop 6 constructs that three-point carrier explicitly.  The elements
  `beta k = ζ^(2k) α²` are proved pairwise distinct, are exactly all roots of
  the irreducible cubic `X³ + 3`, and each generates a degree-three field.
  Thus the three cubic fields in the statement now have a compiled uniform
  presentation.  The next seam is to lift the natural action of each field
  automorphism on these roots to `Equiv.Perm (Fin 3)` and prove faithfulness.

  Solver hop 7 proves the decisive generation identity behind faithfulness:
  `α` is an explicit rational expression in `beta 0` and `beta 1`, hence those
  two cubic conjugates together generate the full splitting field.  The
  identity uses `2ζ² + 1 = α³`, derived from the quadratic relation for `ζ`.
  Consequently an automorphism acting trivially on the three-point carrier is
  forced to be the identity; only the action/API packaging remains before the
  subgroup fixed-field computation.

  Solver hop 8 transports the three cubic roots into the actual splitting
  field subtype as `betaField`.  Their membership, injectivity, and root
  property for the polynomial mapped to `ℚ(α)` are compiled.  This is the
  precise carrier required by `MulAction.toPermHom`; the next step is the
  `Fin 3`/root-set equivalence and conjugation of that permutation action.

  Solver hop 9 completes that packaging. `betaRoot` identifies each indexed
  element with a root-set subtype; injectivity and ambient-complex exhaustion
  prove it bijective, yielding `betaRootEquiv`.  Conjugating the canonical
  automorphism action through this equivalence gives the compiled monoid hom
  `betaActionHom : Aut(ℚ(α)/ℚ) →* Perm (Fin 3)`.  The remaining group-side
  obligation is injectivity (now reducible to `adjoin_two_beta`), followed by
  cardinality-based surjectivity.

  Solver hop 10 closes the entire automorphism-group conjunct.  Equality of
  action permutations gives equality on `beta 0` and `beta 1`; the two-beta
  adjoin theorem and `algHom_ext_of_eq_adjoin` therefore prove the action hom
  injective.  Since both finite groups have cardinality six, the hom is
  bijective and `MulEquiv.ofBijective` yields the required `S₃` equivalence.
  Bridge 3 now uses this result directly.  Its only remaining conjunct is the
  explicit intermediate-field classification via the six transported
  subgroups and their fixed fields.

  Solver hop 11 turns the existential equivalence into the canonical
  `autMulEquiv`, with a simp theorem exposing its action-hom value.  It also
  compiles the exact translations from `beta 0`, `beta 1`, and `beta 2` to the
  three cubic adjoins appearing syntactically in the target.  The remaining
  lattice proof can now transport the alternating subgroup and the three
  point stabilizers through this fixed equivalence without choice ambiguity.

  Solver hop 12 integrates the delegated point-stabilizer result: the preimage
  stabilizer is exactly the fixing subgroup of `ℚ(beta k)`, so its fixed field
  is that cubic adjoin.  The alternating investigation contributed the
  explicit beta-ratio formula for `α³`; locally, `X² + 3` is proved
  irreducible, identified as the minimal polynomial of `α³`, and used to
  compile `finrank ℚ ℚ(α³) = 2`.  The only missing ingredients are the finite
  subgroup census and alternating-subgroup invariance/containment.

  Solver hop 13 compiles the ambient-to-internal transport used by the final
  correspondence argument. `internalField L` is the comap of an embedded
  complex intermediate field to `ℚ(α)`; when `L ≤ ℚ(α)`, mapping it back along
  the subtype inclusion recovers `L`, and equality of two such internal fields
  is equivalent to equality of the originals.  This removes the last ambient
  type mismatch before applying `IsGalois.intermediateFieldEquivSubgroup`.

  Solver hop 14 replaces the failed direct `native_decide` subgroup proof with
  an executable element normal form.  Every permutation of `Fin 3` is now
  compiled as exactly the identity, one of three swaps, or one of the two
  powers of a named three-cycle.  The two even elements are identified
  precisely as `alternatingGroup (Fin 3)`, with their multiplication and
  nontriviality facts compiled.  The remaining census is therefore symbolic
  subgroup closure over these six named elements rather than opaque subgroup
  equality.

  Solver hop 15 completes that symbolic census.  A compiled multiplication
  table supplies all closure calculations, executable membership descriptions
  identify the three point stabilizers, and a case split on the named cycle
  and swaps proves that every subgroup is bottom, one of those stabilizers,
  the alternating subgroup, or top.  What remains is to identify the
  alternating subgroup's fixed field with `ℚ(α³)` and apply the resulting six
  cases through the finite Galois correspondence.

  Solver hop 16 proves the hard containment in that identification.  The two
  further cyclic beta ratios are shown equal to `α³`; consequently every
  automorphism whose permutation is even fixes the embedded element `α³`.
  Thus `ℚ(α³)` is contained in the fixed field of the alternating preimage.
  Equality now reduces solely to the standard degree/cardinality calculation,
  after which the final correspondence case split is formal.

  Solver hop 17 closes that equality.  An explicit equivalence identifies the
  alternating preimage with `A₃`, giving cardinality three.  The tower formula,
  total degree six, and the fixed-field relative-degree theorem give absolute
  fixed-field degree two, matching the compiled degree of `ℚ(α³)`; finite-
  dimensional inclusion therefore yields equality.  Every subgroup in the
  six-case census now has a compiled fixed-field identity, leaving only the
  uniform correspondence transport and ambient-field rewrites.

  Solver hop 18 completes the proof.  An arbitrary internal field is sent to
  its fixing subgroup, transported across `autMulEquiv`, and split by the
  six-subgroup census.  Pullback injectivity and the Galois correspondence
  reduce the cases to the compiled bottom, top, alternating, and stabilizer
  fixed-field identities.  Mapping back along the subtype inclusion and the
  three beta formulas gives exactly the displayed complex intermediate fields.
  All finite computations use kernel-checked `decide`; the final theorem has no
  `sorry` and its axiom audit contains only `propext`, `Classical.choice`, and
  `Quot.sound`.
  -/
  refine ⟨apm_b97A03_bridge_1, ?_⟩
  intro α hα
  rcases apm_b97A03_bridge_2 hα with ⟨hexhaust, -⟩
  rcases apm_b97A03_bridge_3 hα with ⟨haut, hfields⟩
  refine ⟨?_, haut, hfields⟩
  intro z hz
  obtain ⟨k, rfl⟩ := hexhaust z hz
  exact apm_b97a03_zeta_mul_root_mem_field k
