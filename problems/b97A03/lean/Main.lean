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
  simpa [apm_b97a03_polynomial, Polynomial.IsRoot, hpow]

lemma apm_b97a03_zeta_mul_root_mem_field {α : ℂ} (k : ℕ) :
    apm_b97a03_zeta α ^ k * α ∈ apm_b97a03_field α := by
  have hz := apm_b97a03_zeta_mem_field (α := α)
  have ha : α ∈ apm_b97a03_field α := by
    exact IntermediateField.subset_adjoin ℚ {α} (by simp)
  apply IntermediateField.mul_mem
  · induction k with
    | zero => simpa using IntermediateField.one_mem (apm_b97a03_field α)
    | succ k ih =>
        rw [pow_succ]
        exact IntermediateField.mul_mem _ ih hz
  · exact ha

/-- Why this unblocks `apm_b97a03`: this is the independent arithmetic input
needed for the first conjunct; it can be proved by Eisenstein at `3`. -/
theorem apm_b97A03_bridge_1 :
    Irreducible apm_b97a03_polynomial := by
  let f : ℤ[X] := X ^ 6 + C 3
  have hfmonic : f.Monic := by
    dsimp [f]
    exact (monic_X_pow 6).add_of_left (by
      rw [degree_C (by norm_num), degree_X_pow]
      norm_num)
  have hfnat : f.natDegree = 6 := by
    dsimp [f]
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
  have hprime : (Ideal.span ({(3 : ℤ)} : Set ℤ)).IsPrime := by
    exact (Ideal.span_singleton_prime (by norm_num)).2
      (Nat.prime_iff_prime_int.1 (by norm_num))
  have heis : f.IsEisensteinAt (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
    refine hfmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
    · intro n hn
      rw [hfnat] at hn
      simp only [f, coeff_add, coeff_X_pow, coeff_C]
      by_cases hn0 : n = 0
      · subst n
        simp [Ideal.mem_span_singleton]
      · have hn6 : n ≠ 6 := by omega
        simp [hn0, hn6]
    · rw [show f.coeff 0 = 3 by simp [f], Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      norm_num
  have hfirr : Irreducible f :=
    heis.irreducible hprime hfmonic.isPrimitive (by omega)
  have hmap :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfmonic.isPrimitive).mp hfirr
  simpa [apm_b97a03_polynomial, f] using hmap

/-- The six explicit candidates exhaust the roots in `ℂ`. -/
lemma apm_b97a03_candidate_roots_exhaust {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    ∀ z : ℂ,
      (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot z →
        ∃ k : Fin 6, z = apm_b97a03_zeta α ^ (k : ℕ) * α := by
  let candidates : Fin 6 → ℂ :=
    fun k ↦ apm_b97a03_zeta α ^ (k : ℕ) * α
  let e : Fin 6 → apm_b97a03_polynomial.rootSet ℂ := fun k ↦
    ⟨candidates k, by
      rw [Polynomial.mem_rootSet_of_ne apm_b97A03_bridge_1.ne_zero]
      simpa [Polynomial.aeval_def, Polynomial.IsRoot] using
        apm_b97a03_zeta_mul_root hα k⟩
  have heinj : Function.Injective e := by
    intro i j hij
    exact apm_b97a03_candidate_roots_injective hα (congr_arg Subtype.val hij)
  have hnat : apm_b97a03_polynomial.natDegree = 6 := by
    unfold apm_b97a03_polynomial
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
  have hcard : Fintype.card (apm_b97a03_polynomial.rootSet ℂ) = 6 := by
    rw [Polynomial.card_rootSet_eq_natDegree apm_b97A03_bridge_1.separable
      (IsAlgClosed.splits
        (apm_b97a03_polynomial.map (algebraMap ℚ ℂ))), hnat]
  have hesurj : Function.Surjective e :=
    ((Fintype.bijective_iff_injective_and_card e).2 ⟨heinj, by simpa [hcard]⟩).2
  intro z hz
  have hzmem : z ∈ apm_b97a03_polynomial.rootSet ℂ := by
    rw [Polynomial.mem_rootSet_of_ne apm_b97A03_bridge_1.ne_zero]
    simpa [Polynomial.aeval_def, Polynomial.IsRoot] using hz
  obtain ⟨k, hk⟩ := hesurj ⟨z, hzmem⟩
  exact ⟨k, congr_arg Subtype.val hk |>.symm⟩

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
  refine ⟨apm_b97a03_candidate_roots_exhaust hα, ?_⟩
  have hsplits :
      (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).Splits :=
    IsAlgClosed.splits _
  have hadjoin :
      IntermediateField.adjoin ℚ (apm_b97a03_polynomial.rootSet ℂ) =
        apm_b97a03_field α := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro z hz
      have hzroot :
          (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot z := by
        rw [Polynomial.mem_rootSet_of_ne apm_b97A03_bridge_1.ne_zero] at hz
        simpa [Polynomial.aeval_def, Polynomial.IsRoot] using hz
      obtain ⟨k, rfl⟩ := apm_b97a03_candidate_roots_exhaust hα z hzroot
      exact apm_b97a03_zeta_mul_root_mem_field k
    · unfold apm_b97a03_field
      rw [IntermediateField.adjoin_le_iff]
      intro z hz
      rw [Set.mem_singleton_iff.mp hz]
      apply IntermediateField.subset_adjoin
      rw [Polynomial.mem_rootSet_of_ne apm_b97A03_bridge_1.ne_zero]
      simpa [Polynomial.aeval_def, Polynomial.IsRoot] using hα
  rw [← hadjoin]
  exact IntermediateField.adjoin_rootSet_isSplittingField hsplits

lemma apm_b97a03_minpoly_eq {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    minpoly ℚ α = apm_b97a03_polynomial := by
  have hzero : Polynomial.aeval α apm_b97a03_polynomial = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.IsRoot] using hα
  have h := minpoly.eq_of_irreducible apm_b97A03_bridge_1 hzero
  have hmonic : apm_b97a03_polynomial.Monic := by
    unfold apm_b97a03_polynomial
    exact (monic_X_pow 6).add_of_left (by
      rw [degree_C (by norm_num), degree_X_pow]
      norm_num)
  simpa [hmonic.leadingCoeff] using h.symm

lemma apm_b97a03_finrank_field {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ (apm_b97a03_field α) = 6 := by
  have hzero : Polynomial.aeval α apm_b97a03_polynomial = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.IsRoot] using hα
  have hmonic : apm_b97a03_polynomial.Monic := by
    unfold apm_b97a03_polynomial
    exact (monic_X_pow 6).add_of_left (by
      rw [degree_C (by norm_num), degree_X_pow]
      norm_num)
  have hint : IsIntegral ℚ α := ⟨apm_b97a03_polynomial, hmonic, hzero⟩
  rw [apm_b97a03_field, IntermediateField.adjoin.finrank hint,
    apm_b97a03_minpoly_eq hα]
  unfold apm_b97a03_polynomial
  rw [natDegree_add_eq_left_of_natDegree_lt] <;> norm_num

lemma apm_b97a03_card_aut {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Nat.card (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) = 6 := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) :=
    IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable
  rw [IsGalois.card_aut_eq_finrank, apm_b97a03_finrank_field hα]

lemma apm_b97a03_field_eq_rootSet_adjoin {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    apm_b97a03_field α =
      IntermediateField.adjoin ℚ (apm_b97a03_polynomial.rootSet ℂ) := by
  exact (IntermediateField.isSplittingField_iff.mp
    (apm_b97A03_bridge_2 hα).2).2

lemma apm_b97a03_fields_eq_of_roots {α β : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (hβ : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot β) :
    apm_b97a03_field α = apm_b97a03_field β := by
  rw [apm_b97a03_field_eq_rootSet_adjoin hα,
    apm_b97a03_field_eq_rootSet_adjoin hβ]

lemma apm_b97a03_root_isIntegral {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IsIntegral ℚ α := by
  have hzero : Polynomial.aeval α apm_b97a03_polynomial = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.IsRoot] using hα
  have hmonic : apm_b97a03_polynomial.Monic := by
    unfold apm_b97a03_polynomial
    exact (monic_X_pow 6).add_of_left (by
      rw [degree_C (by norm_num), degree_X_pow]
      norm_num)
  exact ⟨apm_b97a03_polynomial, hmonic, hzero⟩

/-- The canonical automorphism taking the chosen root `α` to another root
`β`.  Equality of the two embedded simple fields follows from their common
root-set description as the splitting field. -/
noncomputable def apm_b97a03_autOfRoot {α β : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (hβ : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot β) :
    apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α := by
  unfold apm_b97a03_field
  exact
    (minpoly.algEquiv (apm_b97a03_root_isIntegral hα).isAlgebraic
        ((apm_b97a03_minpoly_eq hα).trans (apm_b97a03_minpoly_eq hβ).symm)).trans
      (AlgEquiv.cast (R := ℚ) (A := fun K : IntermediateField ℚ ℂ ↦ K) (by
        simpa [apm_b97a03_field] using apm_b97a03_fields_eq_of_roots hβ hα))

lemma apm_b97a03_root_mem_field {α β : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (hβ : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot β) :
    β ∈ apm_b97a03_field α := by
  obtain ⟨k, rfl⟩ := apm_b97a03_candidate_roots_exhaust hα β hβ
  exact apm_b97a03_zeta_mul_root_mem_field k

/-- Normality extends the assignment of the chosen root to any conjugate root
to an automorphism of the already identified splitting field. -/
lemma apm_b97a03_exists_aut_apply_root {α β : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (hβ : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot β) :
    ∃ σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α,
      ((σ ⟨α, apm_b97a03_root_mem_field hα hα⟩ : apm_b97a03_field α) : ℂ) = β := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) :=
    IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable
  let a : apm_b97a03_field α := ⟨α, apm_b97a03_root_mem_field hα hα⟩
  let b : apm_b97a03_field α := ⟨β, apm_b97a03_root_mem_field hα hβ⟩
  have hc : IsConjRoot ℚ b a := by
    have hmonic : apm_b97a03_polynomial.Monic := by
      unfold apm_b97a03_polynomial
      exact (monic_X_pow 6).add_of_left (by
        rw [degree_C (by norm_num), degree_X_pow]
        norm_num)
    have hmina : minpoly ℚ a = apm_b97a03_polynomial := by
      have hzero : Polynomial.aeval a apm_b97a03_polynomial = 0 := by
        apply (apm_b97a03_field α).val.injective
        rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂]
        simpa [a, Polynomial.IsRoot] using hα
      have h := minpoly.eq_of_irreducible apm_b97A03_bridge_1 hzero
      simpa [hmonic.leadingCoeff] using h.symm
    have hminb : minpoly ℚ b = apm_b97a03_polynomial := by
      have hzero : Polynomial.aeval b apm_b97a03_polynomial = 0 := by
        apply (apm_b97a03_field α).val.injective
        rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂]
        simpa [b, Polynomial.IsRoot] using hβ
      have h := minpoly.eq_of_irreducible apm_b97A03_bridge_1 hzero
      simpa [hmonic.leadingCoeff] using h.symm
    exact hminb.trans hmina.symm
  obtain ⟨σ, hσ⟩ := hc.exists_algEquiv
  exact ⟨σ, congr_arg Subtype.val hσ⟩

noncomputable def apm_b97a03_normalAutOfRoot {α β : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (hβ : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot β) :
    apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α :=
  Classical.choose (apm_b97a03_exists_aut_apply_root hα hβ)

lemma apm_b97a03_normalAutOfRoot_apply_root {α β : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (hβ : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot β) :
    (((apm_b97a03_normalAutOfRoot hα hβ)
      ⟨α, apm_b97a03_root_mem_field hα hα⟩ : apm_b97a03_field α) : ℂ) = β :=
  Classical.choose_spec (apm_b97a03_exists_aut_apply_root hα hβ)

noncomputable def apm_b97a03_rootAut {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : Fin 6) :
    apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α :=
  apm_b97a03_normalAutOfRoot hα (apm_b97a03_zeta_mul_root hα k)

lemma apm_b97a03_rootAut_apply_root {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : Fin 6) :
    (((apm_b97a03_rootAut hα k)
      ⟨α, apm_b97a03_root_mem_field hα hα⟩ : apm_b97a03_field α) : ℂ) =
        apm_b97a03_zeta α ^ (k : ℕ) * α :=
  apm_b97a03_normalAutOfRoot_apply_root hα (apm_b97a03_zeta_mul_root hα k)

lemma apm_b97a03_rootAut_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective (apm_b97a03_rootAut hα) := by
  intro i j hij
  apply apm_b97a03_candidate_roots_injective hα
  have h := congr_arg
    (fun σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α ↦
      ((σ ⟨α, apm_b97a03_root_mem_field hα hα⟩ : apm_b97a03_field α) : ℂ)) hij
  simpa only [apm_b97a03_rootAut_apply_root] using h

lemma apm_b97a03_rootAut_surjective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Surjective (apm_b97a03_rootAut hα) := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) :=
    IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable
  exact ((apm_b97a03_rootAut_injective hα).bijective_of_nat_card_le (by
    rw [apm_b97a03_card_aut hα, Nat.card_fin])).2

lemma apm_b97a03_aut_ext_root {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    {σ τ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α}
    (h : (((σ ⟨α, apm_b97a03_root_mem_field hα hα⟩ : apm_b97a03_field α) : ℂ)) =
      ((τ ⟨α, apm_b97a03_root_mem_field hα hα⟩ : apm_b97a03_field α) : ℂ)) :
    σ = τ := by
  have he : σ.toAlgHom = τ.toAlgHom := by
    unfold apm_b97a03_field
    apply IntermediateField.adjoin_algHom_ext ℚ
    intro x hx
    have hx' : x = α := Set.mem_singleton_iff.mp hx
    subst x
    apply Subtype.ext
    exact h
  apply AlgEquiv.ext
  intro x
  exact DFunLike.congr_fun he x

lemma apm_b97a03_rootAut_apply_root_pow_three {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : Fin 6) :
    (((apm_b97a03_rootAut hα k)
      (⟨α, apm_b97a03_root_mem_field hα hα⟩ ^ 3) : apm_b97a03_field α) : ℂ) =
        (apm_b97a03_zeta α ^ (k : ℕ) * α) ^ 3 := by
  rw [map_pow]
  exact congr_arg (fun x : ℂ ↦ x ^ 3) (apm_b97a03_rootAut_apply_root hα k)

lemma apm_b97a03_rootAut_apply_zeta {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (k : Fin 6) :
    (((apm_b97a03_rootAut hα k)
      ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ : apm_b97a03_field α) : ℂ) =
        (1 + (apm_b97a03_zeta α ^ (k : ℕ) * α) ^ 3) / 2 := by
  have hzeta :
      (⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ : apm_b97a03_field α) =
        (1 + ⟨α, apm_b97a03_root_mem_field hα hα⟩ ^ 3) / 2 := by
    apply Subtype.ext
    rfl
  have hm :
      (apm_b97a03_rootAut hα k)
          ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ =
        (1 + (apm_b97a03_rootAut hα k)
          ⟨α, apm_b97a03_root_mem_field hα hα⟩ ^ 3) / 2 := by
    rw [hzeta, map_div₀ (apm_b97a03_rootAut hα k),
      map_add (apm_b97a03_rootAut hα k), map_one, map_pow]
    congr 1
    exact map_ofNat (apm_b97a03_rootAut hα k) 2
  rw [congr_arg Subtype.val hm]
  norm_num
  rw [apm_b97a03_rootAut_apply_root]
  change (1 + (apm_b97a03_zeta α ^ (k : ℕ) * α) ^ 3) / (2 : ℂ) = _
  rfl

lemma apm_b97a03_rootAut_apply_zeta_even {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 6) (hk : Even (k : ℕ)) :
    (((apm_b97a03_rootAut hα k)
      ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ : apm_b97a03_field α) : ℂ) =
        apm_b97a03_zeta α := by
  rw [apm_b97a03_rootAut_apply_zeta hα k]
  obtain ⟨j, hj⟩ := hk
  rw [hj]
  have hz6 := apm_b97a03_zeta_pow_six hα
  ring_nf
  rw [show j * 6 = 6 * j by omega, pow_mul, hz6, one_pow, one_mul]
  unfold apm_b97a03_zeta
  ring

lemma apm_b97a03_rootAut_apply_zeta_odd {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 6) (hk : Odd (k : ℕ)) :
    (((apm_b97a03_rootAut hα k)
      ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ : apm_b97a03_field α) : ℂ) =
        1 - apm_b97a03_zeta α := by
  rw [apm_b97a03_rootAut_apply_zeta hα k]
  obtain ⟨j, hj⟩ := hk
  rw [hj]
  have hz6 := apm_b97a03_zeta_pow_six hα
  have hz3 := apm_b97a03_zeta_pow_three hα
  ring_nf
  rw [hz3, show j * 6 = 6 * j by omega, pow_mul, hz6, one_pow]
  unfold apm_b97a03_zeta
  ring

lemma apm_b97a03_one_sub_zeta {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    1 - apm_b97a03_zeta α = apm_b97a03_zeta α ^ 5 := by
  let z := apm_b97a03_zeta α
  have hz0 : z ≠ 0 := (apm_b97a03_zeta_primitive hα).ne_zero (by norm_num)
  apply mul_left_cancel₀ hz0
  have hrel : z ^ 2 - z + 1 = 0 := apm_b97a03_zeta_relation hα
  have hz6 : z ^ 6 = 1 := apm_b97a03_zeta_pow_six hα
  rw [mul_sub, mul_one]
  calc
    z - z * z = 1 := by linear_combination -hrel
    _ = z * z ^ 5 := by rw [← hz6]; ring

noncomputable def apm_b97a03_cubicRoot (α : ℂ) (r : Fin 3) : ℂ :=
  apm_b97a03_zeta α ^ (2 * (r : ℕ)) * α ^ 2

noncomputable def apm_b97a03_cubicPolynomial : ℚ[X] :=
  X ^ 3 + C 3

lemma apm_b97a03_cubicRoot_isRoot {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (r : Fin 3) :
    (apm_b97a03_cubicPolynomial.map (algebraMap ℚ ℂ)).IsRoot
      (apm_b97a03_cubicRoot α r) := by
  have hz6 := apm_b97a03_zeta_pow_six hα
  have ha6 := apm_b97a03_root_pow_six hα
  have hp : apm_b97a03_cubicRoot α r ^ 3 = -3 := by
    unfold apm_b97a03_cubicRoot
    rw [mul_pow, ← pow_mul, show 2 * (r : ℕ) * 3 = 6 * (r : ℕ) by omega,
      pow_mul, hz6, one_pow, one_mul, ← pow_mul,
      show 2 * 3 = 6 by norm_num, ha6]
  simpa [apm_b97a03_cubicPolynomial, Polynomial.IsRoot, hp]

lemma apm_b97a03_cubicRoot_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective (apm_b97a03_cubicRoot α) := by
  have ha : α ≠ 0 := by
    intro ha
    have hpow := apm_b97a03_root_pow_six hα
    rw [ha] at hpow
    norm_num at hpow
  intro i j hij
  unfold apm_b97a03_cubicRoot at hij
  have hp : apm_b97a03_zeta α ^ (2 * (i : ℕ)) =
      apm_b97a03_zeta α ^ (2 * (j : ℕ)) :=
    mul_right_cancel₀ (pow_ne_zero 2 ha) hij
  have he : 2 * (i : ℕ) = 2 * (j : ℕ) :=
    (apm_b97a03_zeta_primitive hα).pow_inj (by omega) (by omega) hp
  apply Fin.ext
  omega

noncomputable def apm_b97a03_cubicRootsEmbedding {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Fin 3 ↪ apm_b97a03_cubicPolynomial.rootSet ℂ where
  toFun r := ⟨apm_b97a03_cubicRoot α r, by
    rw [Polynomial.mem_rootSet_of_ne]
    · simpa [Polynomial.aeval_def, Polynomial.IsRoot] using
        apm_b97a03_cubicRoot_isRoot hα r
    · unfold apm_b97a03_cubicPolynomial
      exact (monic_X_pow 3).add_of_left (by
        rw [degree_C (by norm_num), degree_X_pow]
        norm_num) |>.ne_zero⟩
  inj' i j hij := apm_b97a03_cubicRoot_injective hα (congr_arg Subtype.val hij)

lemma apm_b97a03_cubicRootSet_card {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Fintype.card (apm_b97a03_cubicPolynomial.rootSet ℂ) = 3 := by
  apply le_antisymm
  · let s := apm_b97a03_cubicPolynomial.rootSet ℂ
    let hs : s.Finite := Set.toFinite s
    let e : s ≃ ↑hs.toFinset := Equiv.setCongr (by ext; simp)
    rw [Fintype.card_congr e, Fintype.card_coe,
      ← Set.ncard_eq_toFinset_card s hs]
    simpa [s, apm_b97a03_cubicPolynomial] using
      Polynomial.ncard_rootSet_le apm_b97a03_cubicPolynomial ℂ
  · exact Fintype.card_le_of_injective (apm_b97a03_cubicRootsEmbedding hα)
      (apm_b97a03_cubicRootsEmbedding hα).injective

noncomputable def apm_b97a03_cubicRootsEquiv {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Fin 3 ≃ apm_b97a03_cubicPolynomial.rootSet ℂ :=
  Equiv.ofBijective (apm_b97a03_cubicRootsEmbedding hα)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(apm_b97a03_cubicRootsEmbedding hα).injective,
        by rw [Fintype.card_fin, apm_b97a03_cubicRootSet_card hα]⟩)

lemma apm_b97a03_cubicRoot_mem_field {α : ℂ} (r : Fin 3) :
    apm_b97a03_cubicRoot α r ∈ apm_b97a03_field α := by
  unfold apm_b97a03_cubicRoot
  apply IntermediateField.mul_mem
  · exact IntermediateField.pow_mem _ (apm_b97a03_zeta_mem_field (α := α))
      (2 * (r : ℕ))
  · have ha : α ∈ apm_b97a03_field α :=
      IntermediateField.subset_adjoin ℚ {α} (by simp)
    exact IntermediateField.pow_mem _ ha 2

noncomputable def apm_b97a03_cubicRootsEmbeddingField {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Fin 3 ↪ apm_b97a03_cubicPolynomial.rootSet (apm_b97a03_field α) where
  toFun r :=
    ⟨⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩, by
      have hp0 : apm_b97a03_cubicPolynomial ≠ 0 := by
        unfold apm_b97a03_cubicPolynomial
        exact (monic_X_pow 3).add_of_left (by
          rw [degree_C (by norm_num), degree_X_pow]
          norm_num) |>.ne_zero
      rw [Polynomial.mem_rootSet_of_ne hp0]
      apply (apm_b97a03_field α).val.injective
      rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂]
      simpa [Polynomial.IsRoot] using apm_b97a03_cubicRoot_isRoot hα r⟩
  inj' i j hij := apm_b97a03_cubicRoot_injective hα
    (congr_arg (fun x ↦ (x.1.1 : ℂ)) hij)

lemma apm_b97a03_cubicRootSetField_card {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Fintype.card
      (apm_b97a03_cubicPolynomial.rootSet (apm_b97a03_field α)) = 3 := by
  apply le_antisymm
  · let s := apm_b97a03_cubicPolynomial.rootSet (apm_b97a03_field α)
    let hs : s.Finite := Set.toFinite s
    let e : s ≃ ↑hs.toFinset := Equiv.setCongr (by ext; simp)
    rw [Fintype.card_congr e, Fintype.card_coe,
      ← Set.ncard_eq_toFinset_card s hs]
    simpa [s, apm_b97a03_cubicPolynomial] using
      Polynomial.ncard_rootSet_le apm_b97a03_cubicPolynomial (apm_b97a03_field α)
  · exact Fintype.card_le_of_injective (apm_b97a03_cubicRootsEmbeddingField hα)
      (apm_b97a03_cubicRootsEmbeddingField hα).injective

noncomputable def apm_b97a03_cubicRootsEquivField {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Fin 3 ≃ apm_b97a03_cubicPolynomial.rootSet (apm_b97a03_field α) :=
  Equiv.ofBijective (apm_b97a03_cubicRootsEmbeddingField hα)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨(apm_b97a03_cubicRootsEmbeddingField hα).injective,
        by rw [Fintype.card_fin, apm_b97a03_cubicRootSetField_card hα]⟩)

noncomputable def apm_b97a03_cubicRootPerm {α : ℂ}
    (σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) :
    Equiv.Perm
      (apm_b97a03_cubicPolynomial.rootSet (apm_b97a03_field α)) where
  toFun x := ⟨σ x, Polynomial.rootSet_mapsTo σ.toAlgHom x.2⟩
  invFun x := ⟨σ.symm x, Polynomial.rootSet_mapsTo σ.symm.toAlgHom x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)

noncomputable def apm_b97a03_cubicRootActionHom (α : ℂ) :
    (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) →*
      Equiv.Perm
        (apm_b97a03_cubicPolynomial.rootSet (apm_b97a03_field α)) where
  toFun := apm_b97a03_cubicRootPerm
  map_one' := by
    ext x
    rfl
  map_mul' σ τ := by
    ext x
    rfl

noncomputable def apm_b97a03_finThreeActionHom {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) →* Equiv.Perm (Fin 3) where
  toFun σ := (apm_b97a03_cubicRootsEquivField hα).symm.permCongr
    (apm_b97a03_cubicRootPerm σ)
  map_one' := by
    ext r
    simp [Equiv.permCongr_apply, apm_b97a03_cubicRootPerm]
  map_mul' σ τ := by
    ext r
    simp [Equiv.permCongr_apply, apm_b97a03_cubicRootPerm]

lemma apm_b97a03_finThreeActionHom_fixed {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α)
    (hσ : apm_b97a03_finThreeActionHom hα σ = 1) (r : Fin 3) :
    σ ⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ =
      ⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ := by
  have hr := Equiv.Perm.congr_fun hσ r
  have hr' := congr_arg (apm_b97a03_cubicRootsEquivField hα) hr
  simpa [apm_b97a03_finThreeActionHom, Equiv.permCongr_apply,
    apm_b97a03_cubicRootPerm] using congr_arg Subtype.val hr'

lemma apm_b97a03_finThreeActionHom_injective {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Function.Injective (apm_b97a03_finThreeActionHom hα) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  let a : apm_b97a03_field α :=
    ⟨α, apm_b97a03_root_mem_field hα hα⟩
  let z : apm_b97a03_field α :=
    ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩
  have ha0 : a ≠ 0 := by
    intro ha
    have hcoe := congr_arg (fun x : apm_b97a03_field α ↦ (x : ℂ)) ha
    have hpow := apm_b97a03_root_pow_six hα
    simp [a] at hcoe
    rw [hcoe] at hpow
    norm_num at hpow
  have hfix0 := apm_b97a03_finThreeActionHom_fixed hα σ hσ (0 : Fin 3)
  have ha2 : σ (a ^ 2) = a ^ 2 := by
    simpa [a, apm_b97a03_cubicRoot] using hfix0
  have hfix1 := apm_b97a03_finThreeActionHom_fixed hα σ hσ (1 : Fin 3)
  have hprod : σ (z ^ 2 * a ^ 2) = z ^ 2 * a ^ 2 := by
    simpa [a, z, apm_b97a03_cubicRoot] using hfix1
  have hz2 : σ (z ^ 2) = z ^ 2 := by
    apply mul_right_cancel₀ (pow_ne_zero 2 ha0)
    calc
      σ (z ^ 2) * a ^ 2 = σ (z ^ 2) * σ (a ^ 2) := by rw [ha2]
      _ = σ (z ^ 2 * a ^ 2) := by rw [map_mul]
      _ = z ^ 2 * a ^ 2 := hprod
  have hzrel : z = z ^ 2 + 1 := by
    apply Subtype.ext
    change apm_b97a03_zeta α = apm_b97a03_zeta α ^ 2 + 1
    have hrel := apm_b97a03_zeta_relation hα
    linear_combination -hrel
  have hz : σ z = z := by
    calc
      σ z = σ (z ^ 2 + 1) := congr_arg σ hzrel
      _ = σ (z ^ 2) + 1 := by rw [map_add, map_one]
      _ = z ^ 2 + 1 := by rw [hz2]
      _ = z := hzrel.symm
  have ha3rel : a ^ 3 = 2 * z - 1 := by
    apply Subtype.ext
    change α ^ 3 = 2 * ((1 + α ^ 3) / 2) - 1
    ring
  have ha3 : σ (a ^ 3) = a ^ 3 := by
    calc
      σ (a ^ 3) = σ (2 * z - 1) := congr_arg σ ha3rel
      _ = 2 * σ z - 1 := by
        rw [map_sub, map_mul, map_ofNat, map_one]
      _ = 2 * z - 1 := by rw [hz]
      _ = a ^ 3 := ha3rel.symm
  have harel : a = a ^ 3 / a ^ 2 := by
    field_simp
  have ha : σ a = a := by
    calc
      σ a = σ (a ^ 3 / a ^ 2) := congr_arg σ harel
      _ = σ (a ^ 3) / σ (a ^ 2) := map_div₀ σ _ _
      _ = a ^ 3 / a ^ 2 := by rw [ha3, ha2]
      _ = a := harel.symm
  apply apm_b97a03_aut_ext_root hα
  simpa [a] using congr_arg (fun x : apm_b97a03_field α ↦ (x : ℂ)) ha

noncomputable def apm_b97a03_autEquivPerm {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) ≃*
      Equiv.Perm (Fin 3) := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) :=
    IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable
  apply MulEquiv.ofBijective (apm_b97a03_finThreeActionHom hα)
  exact (apm_b97a03_finThreeActionHom_injective hα).bijective_of_nat_card_le (by
    rw [apm_b97a03_card_aut hα, Nat.card_perm, Nat.card_fin]
    norm_num)

/-- The transposition indexed by its unique fixed point. -/
def apm_b97a03_transposition : Fin 3 → Equiv.Perm (Fin 3) :=
  ![Equiv.swap 1 2, Equiv.swap 0 2, Equiv.swap 0 1]

def apm_b97a03_orderTwoSubgroup (i : Fin 3) :
    Subgroup (Equiv.Perm (Fin 3)) where
  carrier := {g | g = 1 ∨ g = apm_b97a03_transposition i}
  one_mem' := Or.inl rfl
  mul_mem' := by
    fin_cases i <;> decide +revert
  inv_mem' := by
    fin_cases i <;> decide +revert

lemma apm_b97a03_orderTwoSubgroup_card (i : Fin 3) :
    Nat.card (apm_b97a03_orderTwoSubgroup i) = 2 := by
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨1, Or.inl rfl⟩,
    ⟨apm_b97a03_transposition i, Or.inr rfl⟩, ?_, ?_⟩
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

lemma apm_b97a03_transposition_ne_one (i : Fin 3) :
    apm_b97a03_transposition i ≠ 1 := by
  fin_cases i <;> decide

lemma apm_b97a03_orderTwoSubgroup_injective :
    Function.Injective apm_b97a03_orderTwoSubgroup := by
  intro i j
  classical
  intro h
  have hm : apm_b97a03_transposition i ∈ apm_b97a03_orderTwoSubgroup j := by
    rw [← h]
    exact Or.inr rfl
  change apm_b97a03_transposition i = 1 ∨
    apm_b97a03_transposition i = apm_b97a03_transposition j at hm
  rcases hm with hm | hm
  · exact (apm_b97a03_transposition_ne_one i hm).elim
  · fin_cases i <;> fin_cases j
    all_goals first | rfl | (revert hm; decide)

lemma apm_b97a03_alternatingGroup_card :
    Nat.card (alternatingGroup (Fin 3)) = 3 := by
  rw [nat_card_alternatingGroup]
  norm_num

lemma apm_b97a03_perm_cases (g : Equiv.Perm (Fin 3)) :
    g = 1 ∨ (∃ i, g = apm_b97a03_transposition i) ∨
      g = apm_b97a03_transposition 0 * apm_b97a03_transposition 1 ∨
      g = apm_b97a03_transposition 1 * apm_b97a03_transposition 0 := by
  revert g
  decide

lemma apm_b97a03_transposition_order (i : Fin 3) :
    orderOf (apm_b97a03_transposition i) = 2 := by
  apply (orderOf_eq_iff (by norm_num)).2
  constructor
  · fin_cases i <;> decide
  · intro m hm hm0
    interval_cases m
    all_goals fin_cases i <;> decide

lemma apm_b97a03_cycle_order :
    orderOf (apm_b97a03_transposition 0 * apm_b97a03_transposition 1) = 3 ∧
    orderOf (apm_b97a03_transposition 1 * apm_b97a03_transposition 0) = 3 := by
  constructor <;> apply (orderOf_eq_iff (by norm_num)).2 <;> constructor
  · decide
  · intro m hm hm0
    interval_cases m <;> decide
  · decide
  · intro m hm hm0
    interval_cases m <;> decide

lemma apm_b97a03_cycles_mem_alternating :
    apm_b97a03_transposition 0 * apm_b97a03_transposition 1 ∈
      alternatingGroup (Fin 3) ∧
    apm_b97a03_transposition 1 * apm_b97a03_transposition 0 ∈
      alternatingGroup (Fin 3) := by
  constructor <;> rw [Equiv.Perm.mem_alternatingGroup] <;> decide

/-- The complete subgroup lattice of `S₃`. -/
lemma apm_b97a03_S3_subgroup_classification
    (H : Subgroup (Equiv.Perm (Fin 3))) :
    H = ⊥ ∨ H = alternatingGroup (Fin 3) ∨
      (∃ i, H = apm_b97a03_orderTwoSubgroup i) ∨ H = ⊤ := by
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
    rcases apm_b97a03_perm_cases g with hg | ⟨i, hg⟩ | hg | hg
    · exact False.elim (hg1 hg)
    · subst g
      refine ⟨i, ?_⟩
      symm
      apply Subgroup.eq_of_le_of_card_ge
      · intro x hx
        rcases hx with hx | hx
        · simp [hx]
        · simpa [hx] using hgH
      · rw [apm_b97a03_orderTwoSubgroup_card, h2]
    · subst g
      have hd3 := H.orderOf_dvd_natCard hgH
      rw [apm_b97a03_cycle_order.1, h2] at hd3
      norm_num at hd3
    · subst g
      have hd3 := H.orderOf_dvd_natCard hgH
      rw [apm_b97a03_cycle_order.2, h2] at hd3
      norm_num at hd3
  · right; left
    have hle : H ≤ alternatingGroup (Fin 3) := by
      intro g hgH
      rcases apm_b97a03_perm_cases g with hg | ⟨i, hg⟩ | hg | hg
      · rw [hg]
        exact Subgroup.one_mem _
      · subst g
        have hd2 := H.orderOf_dvd_natCard hgH
        rw [apm_b97a03_transposition_order, h3] at hd2
        norm_num at hd2
      · simpa [hg] using apm_b97a03_cycles_mem_alternating.1
      · simpa [hg] using apm_b97a03_cycles_mem_alternating.2
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [apm_b97a03_alternatingGroup_card, h3]
  · right; right; right
    exact H.eq_top_of_card_eq (h6.trans hcardG.symm)

lemma apm_b97a03_subgroup_eq_alternating_of_card_eq_three
    (H : Subgroup (Equiv.Perm (Fin 3))) (hH : Nat.card H = 3) :
    H = alternatingGroup (Fin 3) := by
  rcases apm_b97a03_S3_subgroup_classification H with
    hbot | halt | htwo | htop
  · rw [hbot, Subgroup.card_bot] at hH
    omega
  · exact halt
  · obtain ⟨i, rfl⟩ := htwo
    rw [apm_b97a03_orderTwoSubgroup_card] at hH
    omega
  · have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      norm_num
    have htopcard : Nat.card (⊤ : Subgroup (Equiv.Perm (Fin 3))) = 6 := by
      simpa using hcard
    rw [htop, htopcard] at hH
    omega

/-- Galois correspondence reduces every intermediate field inside the
splitting field to the four nontrivial subgroup cases of `S₃`. -/
lemma apm_b97a03_intermediateField_cases {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (E : IntermediateField ℚ (apm_b97a03_field α)) :
    let e := apm_b97a03_autEquivPerm hα
    let H₂ := e.comapSubgroup (alternatingGroup (Fin 3))
    let H₃ := fun i : Fin 3 ↦ e.comapSubgroup (apm_b97a03_orderTwoSubgroup i)
    E = ⊥ ∨ E = IntermediateField.fixedField H₂ ∨
      (∃ i, E = IntermediateField.fixedField (H₃ i)) ∨ E = ⊤ := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) :=
    IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable
  let e := apm_b97a03_autEquivPerm hα
  let H₂ : Subgroup (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) :=
    e.comapSubgroup (alternatingGroup (Fin 3))
  let H₃ (i : Fin 3) :
      Subgroup (apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) :=
    e.comapSubgroup (apm_b97a03_orderTwoSubgroup i)
  rcases apm_b97a03_S3_subgroup_classification
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
      change Subgroup.map e.toMonoidHom E.fixingSubgroup =
        Subgroup.map e.toMonoidHom
          (Subgroup.comap e.toMonoidHom (alternatingGroup (Fin 3)))
      exact halt.trans
        (Subgroup.map_comap_eq_self_of_surjective e.surjective _).symm
    exact congrArg IntermediateField.fixedField hfix
  · rcases hthree with ⟨i, hi⟩
    right; right; left
    refine ⟨i, ?_⟩
    rw [← IsGalois.fixedField_fixingSubgroup (K := E)]
    have hfix : E.fixingSubgroup = H₃ i := by
      apply e.mapSubgroup.injective
      dsimp only [H₃]
      change Subgroup.map e.toMonoidHom E.fixingSubgroup =
        Subgroup.map e.toMonoidHom
          (Subgroup.comap e.toMonoidHom (apm_b97a03_orderTwoSubgroup i))
      exact hi.trans
        (Subgroup.map_comap_eq_self_of_surjective e.surjective _).symm
    exact congrArg IntermediateField.fixedField hfix
  · left
    rw [← IsGalois.fixedField_fixingSubgroup (K := E)]
    have hfix : E.fixingSubgroup = ⊤ := by
      apply e.mapSubgroup.injective
      simpa using htop
    rw [hfix, IsGalois.fixedField_top]

lemma apm_b97a03_mem_fixingSubgroup_adjoin_singleton
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (x : E) (σ : E ≃ₐ[F] E) :
    σ ∈ (IntermediateField.adjoin F {x}).fixingSubgroup ↔ σ x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h x (IntermediateField.subset_adjoin F {x} (Set.mem_singleton x))
  · intro h y hy
    refine IntermediateField.adjoin_induction F ?_ ?_ ?_ ?_ ?_ hy
    · intro z hz
      simpa [Set.mem_singleton_iff.mp hz] using h
    · intro z
      exact σ.commutes z
    · intro z w _ _ hz hw
      simp [hz, hw]
    · intro z _ hz
      simp [hz]
    · intro z w _ _ hz hw
      simp [hz, hw]

lemma apm_b97a03_mem_orderTwoSubgroup_iff_fixed
    (r : Fin 3) (g : Equiv.Perm (Fin 3)) :
    g ∈ apm_b97a03_orderTwoSubgroup r ↔ g r = r := by
  change (g = 1 ∨ g = apm_b97a03_transposition r) ↔ g r = r
  rcases apm_b97a03_perm_cases g with hg | ⟨i, hg⟩ | hg | hg
  · subst g
    fin_cases r <;> decide
  · subst g
    fin_cases i <;> fin_cases r <;> decide
  · subst g
    fin_cases r <;> decide
  · subst g
    fin_cases r <;> decide

lemma apm_b97a03_autEquivPerm_fixed_iff {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (σ : apm_b97a03_field α ≃ₐ[ℚ] apm_b97a03_field α) (r : Fin 3) :
    apm_b97a03_autEquivPerm hα σ r = r ↔
      σ ⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ =
        ⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ := by
  change (apm_b97a03_finThreeActionHom hα σ) r = r ↔ _
  constructor
  · intro hr
    have hr' := congrArg (apm_b97a03_cubicRootsEquivField hα) hr
    simpa [apm_b97a03_finThreeActionHom, Equiv.permCongr_apply,
        apm_b97a03_cubicRootPerm, apm_b97a03_cubicRootsEquivField,
        apm_b97a03_cubicRootsEmbeddingField] using congrArg Subtype.val hr'
  · intro hr
    apply (apm_b97a03_cubicRootsEquivField hα).injective
    apply Subtype.ext
    simpa [apm_b97a03_finThreeActionHom, Equiv.permCongr_apply,
      apm_b97a03_cubicRootPerm, apm_b97a03_cubicRootsEquivField,
      apm_b97a03_cubicRootsEmbeddingField] using hr

lemma apm_b97a03_cubicRoot_fixingSubgroup {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (r : Fin 3) :
    (IntermediateField.adjoin ℚ
      {⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩}).fixingSubgroup =
      (apm_b97a03_autEquivPerm hα).comapSubgroup
        (apm_b97a03_orderTwoSubgroup r) := by
  ext σ
  change σ ∈ (IntermediateField.adjoin ℚ
      {⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩}).fixingSubgroup ↔
    apm_b97a03_autEquivPerm hα σ ∈ apm_b97a03_orderTwoSubgroup r
  rw [apm_b97a03_mem_fixingSubgroup_adjoin_singleton,
    apm_b97a03_mem_orderTwoSubgroup_iff_fixed,
    apm_b97a03_autEquivPerm_fixed_iff]

lemma apm_b97a03_cubicRoot_fixedField {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) (r : Fin 3) :
    IntermediateField.fixedField
        ((apm_b97a03_autEquivPerm hα).comapSubgroup
          (apm_b97a03_orderTwoSubgroup r)) =
      IntermediateField.adjoin ℚ
        {⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩} := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) :=
    IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable
  let C : IntermediateField ℚ (apm_b97a03_field α) :=
    IntermediateField.adjoin ℚ
      {⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩}
  calc
    IntermediateField.fixedField
        ((apm_b97a03_autEquivPerm hα).comapSubgroup
          (apm_b97a03_orderTwoSubgroup r)) =
        IntermediateField.fixedField C.fixingSubgroup := by
          exact congrArg IntermediateField.fixedField
            (apm_b97a03_cubicRoot_fixingSubgroup hα r).symm
    _ = C := IsGalois.fixedField_fixingSubgroup C

noncomputable def apm_b97a03_quadraticPolynomial : ℚ[X] := X ^ 2 + C 3

lemma apm_b97a03_quadraticPolynomial_irreducible :
    Irreducible apm_b97a03_quadraticPolynomial := by
  let f : ℤ[X] := X ^ 2 + C 3
  have hfmonic : f.Monic := by
    dsimp [f]
    exact (monic_X_pow 2).add_of_left (by
      rw [degree_C (by norm_num), degree_X_pow]
      norm_num)
  have hfnat : f.natDegree = 2 := by
    dsimp [f]
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> norm_num
  have hprime : (Ideal.span ({(3 : ℤ)} : Set ℤ)).IsPrime := by
    exact (Ideal.span_singleton_prime (by norm_num)).2
      (Nat.prime_iff_prime_int.1 (by norm_num))
  have heis : f.IsEisensteinAt (Ideal.span ({(3 : ℤ)} : Set ℤ)) := by
    refine hfmonic.isEisensteinAt_of_mem_of_notMem hprime.ne_top ?_ ?_
    · intro n hn
      rw [hfnat] at hn
      simp only [f, coeff_add, coeff_X_pow, coeff_C]
      by_cases hn0 : n = 0
      · subst n
        simp [Ideal.mem_span_singleton]
      · have hn2 : n ≠ 2 := by omega
        simp [hn0, hn2]
    · rw [show f.coeff 0 = 3 by simp [f], Ideal.span_singleton_pow,
        Ideal.mem_span_singleton]
      norm_num
  have hfirr : Irreducible f :=
    heis.irreducible hprime hfmonic.isPrimitive (by omega)
  have hmap :=
    (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hfmonic.isPrimitive).mp hfirr
  simpa [apm_b97a03_quadraticPolynomial, f] using hmap

lemma apm_b97a03_minpoly_rootCube {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    minpoly ℚ
      (⟨α ^ 3, (apm_b97a03_field α).pow_mem
        (apm_b97a03_root_mem_field hα hα) 3⟩ : apm_b97a03_field α) =
      apm_b97a03_quadraticPolynomial := by
  let b : apm_b97a03_field α :=
    ⟨α ^ 3, (apm_b97a03_field α).pow_mem
      (apm_b97a03_root_mem_field hα hα) 3⟩
  have hzero : Polynomial.aeval b apm_b97a03_quadraticPolynomial = 0 := by
    apply (apm_b97a03_field α).val.injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂]
    have hc : (α ^ 3) ^ 2 + 3 = 0 := by
      linear_combination apm_b97a03_root_pow_three_sq hα
    simpa [b, apm_b97a03_quadraticPolynomial] using hc
  have h := minpoly.eq_of_irreducible
    apm_b97a03_quadraticPolynomial_irreducible hzero
  have hmonic : apm_b97a03_quadraticPolynomial.Monic := by
    unfold apm_b97a03_quadraticPolynomial
    exact (monic_X_pow 2).add_of_left (by
      rw [degree_C (by norm_num), degree_X_pow]
      norm_num)
  simpa [hmonic.leadingCoeff] using h.symm

lemma apm_b97a03_rootCube_adjoin_finrank {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      {(⟨α ^ 3, (apm_b97a03_field α).pow_mem
        (apm_b97a03_root_mem_field hα hα) 3⟩ : apm_b97a03_field α)}) = 2 := by
  let b : apm_b97a03_field α :=
    ⟨α ^ 3, (apm_b97a03_field α).pow_mem
      (apm_b97a03_root_mem_field hα hα) 3⟩
  have hbzero : Polynomial.aeval b apm_b97a03_quadraticPolynomial = 0 := by
    apply (apm_b97a03_field α).val.injective
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂]
    have hc : (α ^ 3) ^ 2 + 3 = 0 := by
      linear_combination apm_b97a03_root_pow_three_sq hα
    simpa [b, apm_b97a03_quadraticPolynomial] using hc
  have hbmonic : apm_b97a03_quadraticPolynomial.Monic := by
    unfold apm_b97a03_quadraticPolynomial
    exact (monic_X_pow 2).add_of_left (by
      rw [degree_C (by norm_num), degree_X_pow]
      norm_num)
  have hb : IsIntegral ℚ b := ⟨apm_b97a03_quadraticPolynomial, hbmonic, hbzero⟩
  rw [IntermediateField.adjoin.finrank hb, apm_b97a03_minpoly_rootCube hα]
  norm_num [apm_b97a03_quadraticPolynomial]

lemma apm_b97a03_rootCube_fixedField {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α) :
    IntermediateField.fixedField
        ((apm_b97a03_autEquivPerm hα).comapSubgroup
          (alternatingGroup (Fin 3))) =
      IntermediateField.adjoin ℚ
        {(⟨α ^ 3, (apm_b97a03_field α).pow_mem
          (apm_b97a03_root_mem_field hα hα) 3⟩ : apm_b97a03_field α)} := by
  letI : Polynomial.IsSplittingField ℚ (apm_b97a03_field α)
      apm_b97a03_polynomial := (apm_b97A03_bridge_2 hα).2
  letI : FiniteDimensional ℚ (apm_b97a03_field α) :=
    Polynomial.IsSplittingField.finiteDimensional _ apm_b97a03_polynomial
  letI : IsGalois ℚ (apm_b97a03_field α) :=
    IsGalois.of_separable_splitting_field apm_b97A03_bridge_1.separable
  let C : IntermediateField ℚ (apm_b97a03_field α) :=
    IntermediateField.adjoin ℚ
      {(⟨α ^ 3, (apm_b97a03_field α).pow_mem
        (apm_b97a03_root_mem_field hα hα) 3⟩ : apm_b97a03_field α)}
  let e := apm_b97a03_autEquivPerm hα
  have hrel : Module.finrank C (apm_b97a03_field α) = 3 := by
    have htower := Module.finrank_mul_finrank ℚ C (apm_b97a03_field α)
    have hC : Module.finrank ℚ C = 2 := apm_b97a03_rootCube_adjoin_finrank hα
    rw [hC, apm_b97a03_finrank_field hα] at htower
    nlinarith [Module.finrank_pos (R := C) (M := apm_b97a03_field α)]
  have hcardFix : Nat.card C.fixingSubgroup = 3 := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    exact hrel
  have hcardMap : Nat.card (e.mapSubgroup C.fixingSubgroup) = 3 := by
    calc
      Nat.card (e.mapSubgroup C.fixingSubgroup) = Nat.card C.fixingSubgroup :=
        (Nat.card_congr (e.subgroupMap C.fixingSubgroup).toEquiv).symm
      _ = 3 := hcardFix
  have hmap : e.mapSubgroup C.fixingSubgroup = alternatingGroup (Fin 3) :=
    apm_b97a03_subgroup_eq_alternating_of_card_eq_three _ hcardMap
  have hfix : C.fixingSubgroup = e.comapSubgroup (alternatingGroup (Fin 3)) := by
    apply e.mapSubgroup.injective
    change e.mapSubgroup C.fixingSubgroup =
      e.mapSubgroup (e.comapSubgroup (alternatingGroup (Fin 3)))
    exact hmap.trans
      (Subgroup.map_comap_eq_self_of_surjective e.surjective _).symm
  calc
    IntermediateField.fixedField
        (e.comapSubgroup (alternatingGroup (Fin 3))) =
        IntermediateField.fixedField C.fixingSubgroup :=
      congrArg IntermediateField.fixedField hfix.symm
    _ = C := IsGalois.fixedField_fixingSubgroup C

lemma apm_b97a03_rootAut_apply_cubicRoot_even {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 6) (hk : Even (k : ℕ)) (r : Fin 3) :
    (((apm_b97a03_rootAut hα k)
      ⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ :
        apm_b97a03_field α) : ℂ) =
      apm_b97a03_zeta α ^ (2 * (r : ℕ)) *
        (apm_b97a03_zeta α ^ (k : ℕ) * α) ^ 2 := by
  have hre :
      (⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ :
        apm_b97a03_field α) =
      ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ ^ (2 * (r : ℕ)) *
        ⟨α, apm_b97a03_root_mem_field hα hα⟩ ^ 2 := by
    apply Subtype.ext
    rfl
  have hm := congr_arg (apm_b97a03_rootAut hα k) hre
  rw [map_mul, map_pow, map_pow] at hm
  rw [congr_arg Subtype.val hm]
  change
    (((apm_b97a03_rootAut hα k)
      ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ :
        apm_b97a03_field α) : ℂ) ^ (2 * (r : ℕ)) *
      (((apm_b97a03_rootAut hα k)
      ⟨α, apm_b97a03_root_mem_field hα hα⟩ :
        apm_b97a03_field α) : ℂ) ^ 2 = _
  rw [apm_b97a03_rootAut_apply_zeta_even hα k hk,
    apm_b97a03_rootAut_apply_root]

lemma apm_b97a03_rootAut_apply_cubicRoot_odd {α : ℂ}
    (hα : (apm_b97a03_polynomial.map (algebraMap ℚ ℂ)).IsRoot α)
    (k : Fin 6) (hk : Odd (k : ℕ)) (r : Fin 3) :
    (((apm_b97a03_rootAut hα k)
      ⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ :
        apm_b97a03_field α) : ℂ) =
      apm_b97a03_zeta α ^ (10 * (r : ℕ)) *
        (apm_b97a03_zeta α ^ (k : ℕ) * α) ^ 2 := by
  have hre :
      (⟨apm_b97a03_cubicRoot α r, apm_b97a03_cubicRoot_mem_field r⟩ :
        apm_b97a03_field α) =
      ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ ^ (2 * (r : ℕ)) *
        ⟨α, apm_b97a03_root_mem_field hα hα⟩ ^ 2 := by
    apply Subtype.ext
    rfl
  have hm := congr_arg (apm_b97a03_rootAut hα k) hre
  rw [map_mul, map_pow, map_pow] at hm
  rw [congr_arg Subtype.val hm]
  change
    (((apm_b97a03_rootAut hα k)
      ⟨apm_b97a03_zeta α, apm_b97a03_zeta_mem_field⟩ :
        apm_b97a03_field α) : ℂ) ^ (2 * (r : ℕ)) *
      (((apm_b97a03_rootAut hα k)
      ⟨α, apm_b97a03_root_mem_field hα hα⟩ :
        apm_b97a03_field α) : ℂ) ^ 2 = _
  rw [apm_b97a03_rootAut_apply_zeta_odd hα k hk,
    apm_b97a03_one_sub_zeta hα, ← pow_mul,
    show 5 * (2 * (r : ℕ)) = 10 * (r : ℕ) by omega,
    apm_b97a03_rootAut_apply_root]

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
  constructor
  · exact ⟨apm_b97a03_autEquivPerm hα⟩
  · intro L hL
    let K : IntermediateField ℚ ℂ := apm_b97a03_field α
    let E : IntermediateField ℚ K := L.comap K.val
    have hLift : IntermediateField.lift E = L := by
      apply IntermediateField.map_comap_eq_self
      intro x hx
      exact ⟨⟨x, hL hx⟩, rfl⟩
    rcases apm_b97a03_intermediateField_cases hα E with
      hbot | halt | hcubic | htop
    · left
      rw [← hLift, hbot]
      change (⊥ : IntermediateField ℚ K).map K.val = ⊥
      exact IntermediateField.map_bot K.val
    · right; left
      have halt' : E = IntermediateField.adjoin ℚ
          {(⟨α ^ 3, (apm_b97a03_field α).pow_mem
            (apm_b97a03_root_mem_field hα hα) 3⟩ : K)} :=
        halt.trans (apm_b97a03_rootCube_fixedField hα)
      have hamb := congrArg
        (fun A : IntermediateField ℚ K ↦ IntermediateField.lift A) halt'
      change IntermediateField.lift E = IntermediateField.lift
        (IntermediateField.adjoin ℚ
          {(⟨α ^ 3, (apm_b97a03_field α).pow_mem
            (apm_b97a03_root_mem_field hα hα) 3⟩ : K)}) at hamb
      rw [hLift, IntermediateField.lift_adjoin_simple] at hamb
      simpa using hamb
    · rcases hcubic with ⟨r, hr⟩
      have hr' : E = IntermediateField.adjoin ℚ
          {⟨apm_b97a03_cubicRoot α r,
            apm_b97a03_cubicRoot_mem_field r⟩} :=
        hr.trans (apm_b97a03_cubicRoot_fixedField hα r)
      have hamb := congrArg
        (fun A : IntermediateField ℚ K ↦ IntermediateField.lift A) hr'
      change IntermediateField.lift E = IntermediateField.lift
        (IntermediateField.adjoin ℚ
          {⟨apm_b97a03_cubicRoot α r,
            apm_b97a03_cubicRoot_mem_field r⟩}) at hamb
      rw [hLift, IntermediateField.lift_adjoin_simple] at hamb
      fin_cases r
      · right; right; left
        simpa [apm_b97a03_cubicRoot] using hamb
      · right; right; right; left
        simpa [apm_b97a03_cubicRoot] using hamb
      · right; right; right; right; left
        simpa [apm_b97a03_cubicRoot] using hamb
    · right; right; right; right; right
      rw [← hLift, htop]
      change (⊤ : IntermediateField ℚ K).map K.val = apm_b97a03_field α
      calc
        (⊤ : IntermediateField ℚ K).map K.val = K.val.fieldRange :=
          (AlgHom.fieldRange_eq_map K.val).symm
        _ = K := K.fieldRange_val
        _ = apm_b97a03_field α := rfl

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
  refine ⟨apm_b97A03_bridge_1, ?_⟩
  intro α hα
  obtain ⟨hroots, -⟩ := apm_b97A03_bridge_2 hα
  obtain ⟨haut, hfields⟩ := apm_b97A03_bridge_3 hα
  refine ⟨?_, haut, hfields⟩
  intro z hz
  obtain ⟨k, rfl⟩ := hroots z hz
  exact apm_b97a03_zeta_mul_root_mem_field k
