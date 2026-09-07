import Mathlib

/-!
# APM b93J04

## Statement repairs

None.

## Encoding questions

None. The splitting field is quantified abstractly; the witnesses `r₂` and
`r₃` encode `√2` and `√3`, so the basis, automorphism action, and complete
intermediate-field list are stated inside the actual splitting field.
-/

open Polynomial

/-- The polynomial `X⁴ - 10X² + 1` over `ℚ`. -/
noncomputable def apm_b93j04_poly : Polynomial ℚ :=
  X ^ 4 - C 10 * X ^ 2 + C 1

lemma apm_b93j04_poly_monic : apm_b93j04_poly.Monic := by
  rw [apm_b93j04_poly, sub_eq_add_neg, add_assoc]
  apply monic_X_pow_add
  calc
    (-(C 10 * X ^ 2) + (1 : Polynomial ℚ)).degree ≤
        max (-(C 10 * X ^ 2) : Polynomial ℚ).degree (1 : Polynomial ℚ).degree :=
      degree_add_le _ _
    _ ≤ 2 := by norm_num
    _ < 4 := by norm_num

lemma apm_b93j04_poly_natDegree : apm_b93j04_poly.natDegree = 4 := by
  have hlow : (-(C 10 * X ^ 2) + (1 : Polynomial ℚ)).degree < 4 := by
    calc
      (-(C 10 * X ^ 2) + (1 : Polynomial ℚ)).degree ≤
          max (-(C 10 * X ^ 2) : Polynomial ℚ).degree (1 : Polynomial ℚ).degree :=
        degree_add_le _ _
      _ ≤ 2 := by norm_num
      _ < 4 := by norm_num
  rw [apm_b93j04_poly, sub_eq_add_neg, add_assoc]
  have hlow' : (-(C 10 * X ^ 2) + (1 : Polynomial ℚ)).degree <
      (X ^ 4 : Polynomial ℚ).degree := by simpa using hlow
  exact (natDegree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt hlow')).trans
    (by simp)

/-- The radical description used by the informal solution really gives roots
of the quartic, over any characteristic-zero target field. -/
lemma apm_b93j04_radical_root
    (K : Type*) [Field K] [Algebra ℚ K]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) :
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly = 0 := by
  have hs : (r₂ + r₃) ^ 2 - algebraMap ℚ K 5 = 2 * r₂ * r₃ := by
    rw [show algebraMap ℚ K 5 = algebraMap ℚ K 2 + algebraMap ℚ K 3 by norm_num]
    rw [← h₂, ← h₃]
    ring
  calc
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly =
        ((r₂ + r₃) ^ 2 - algebraMap ℚ K 5) ^ 2 - algebraMap ℚ K 24 := by
          simp [apm_b93j04_poly]
          ring
    _ = (2 * r₂ * r₃) ^ 2 - algebraMap ℚ K 24 := by rw [hs]
    _ = 0 := by
      rw [show (2 * r₂ * r₃) ^ 2 =
          (algebraMap ℚ K 4) * (r₂ ^ 2) * (r₃ ^ 2) by norm_num; ring]
      rw [h₂, h₃]
      norm_num

/-- All four sign combinations of the two radicals are roots.  This packages
the complete explicit candidate root set needed by the splitting-field
argument, rather than reproving the quartic identity for each sign choice. -/
lemma apm_b93j04_four_radical_roots
    (K : Type*) [Field K] [Algebra ℚ K]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) :
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly = 0 ∧
    Polynomial.eval₂ (algebraMap ℚ K) (r₂ - r₃) apm_b93j04_poly = 0 ∧
    Polynomial.eval₂ (algebraMap ℚ K) (-r₂ + r₃) apm_b93j04_poly = 0 ∧
    Polynomial.eval₂ (algebraMap ℚ K) (-r₂ - r₃) apm_b93j04_poly = 0 := by
  have hn₂ : (-r₂) ^ 2 = algebraMap ℚ K 2 := by simpa using h₂
  have hn₃ : (-r₃) ^ 2 = algebraMap ℚ K 3 := by simpa using h₃
  exact ⟨apm_b93j04_radical_root K r₂ r₃ h₂ h₃,
    by simpa [sub_eq_add_neg] using apm_b93j04_radical_root K r₂ (-r₃) h₂ hn₃,
    apm_b93j04_radical_root K (-r₂) r₃ hn₂ h₃,
    by simpa [sub_eq_add_neg] using apm_b93j04_radical_root K (-r₂) (-r₃) hn₂ hn₃⟩

/-- The four radical candidates are pairwise distinct.  This is the missing
separability-free input needed to turn the four root computations into root-
set exhaustion for the quartic. -/
lemma apm_b93j04_four_radical_roots_pairwise
    (K : Type*) [Field K] [Algebra ℚ K]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) :
    r₂ + r₃ ≠ r₂ - r₃ ∧
    r₂ + r₃ ≠ -r₂ + r₃ ∧
    r₂ + r₃ ≠ -r₂ - r₃ ∧
    r₂ - r₃ ≠ -r₂ + r₃ ∧
    r₂ - r₃ ≠ -r₂ - r₃ ∧
    -r₂ + r₃ ≠ -r₂ - r₃ := by
  have htwo : (2 : K) ≠ 0 := by
    intro h
    have hh : algebraMap ℚ K 2 = algebraMap ℚ K 0 := by simpa using h
    have := (algebraMap ℚ K).injective hh
    norm_num at this
  have hr₂ : r₂ ≠ 0 := by
    intro h
    rw [h] at h₂
    have hh : algebraMap ℚ K 0 = algebraMap ℚ K 2 := by simpa using h₂
    have := (algebraMap ℚ K).injective hh
    norm_num at this
  have hr₃ : r₃ ≠ 0 := by
    intro h
    rw [h] at h₃
    have hh : algebraMap ℚ K 0 = algebraMap ℚ K 3 := by simpa using h₃
    have := (algebraMap ℚ K).injective hh
    norm_num at this
  have hr₂r₃ : r₂ ≠ r₃ := by
    intro h
    rw [h] at h₂
    rw [h₂] at h₃
    have := (algebraMap ℚ K).injective h₃
    norm_num at this
  have hr₂nr₃ : r₂ ≠ -r₃ := by
    intro h
    rw [h] at h₂
    have : (-r₃) ^ 2 = r₃ ^ 2 := by ring
    rw [this, h₃] at h₂
    have := (algebraMap ℚ K).injective h₂
    norm_num at this
  constructor
  · intro h
    apply hr₃
    apply mul_left_cancel₀ (a := (2 : K)) htwo
    linear_combination h
  constructor
  · intro h
    apply hr₂
    apply mul_left_cancel₀ (a := (2 : K)) htwo
    linear_combination h
  constructor
  · intro h
    apply hr₂nr₃
    apply mul_left_cancel₀ (a := (2 : K)) htwo
    linear_combination h
  constructor
  · intro h
    apply hr₂r₃
    apply mul_left_cancel₀ (a := (2 : K)) htwo
    linear_combination h
  constructor
  · intro h
    apply hr₂
    apply mul_left_cancel₀ (a := (2 : K)) htwo
    linear_combination h
  · intro h
    apply hr₃
    apply mul_left_cancel₀ (a := (2 : K)) htwo
    linear_combination h

/-- Once the abstract automorphism group has the two numerical Klein-four
invariants, Mathlib supplies exactly the group equivalence frozen below. -/
lemma apm_b93J04_mulEquiv_kleinFour_of_card_exponent
    (G : Type*) [Group G]
    (hcard : Nat.card G = 4) (hexp : Monoid.exponent G = 2) :
    Nonempty (G ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  letI : IsKleinFour G := ⟨hcard, hexp⟩
  rcases (IsKleinFour.nonempty_mulEquiv :
    Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2))) with ⟨e⟩
  exact ⟨e.trans (MulEquiv.prodMultiplicative (ZMod 2) (ZMod 2))⟩

/-- A group exhausted by two involutions and their product has exactly the
five subgroups expected of the Klein four-group. -/
lemma apm_b93j04_subgroup_five_cases
    (G : Type*) [Group G] (σ τ : G)
    (hσsq : σ ^ 2 = 1) (hτsq : τ ^ 2 = 1)
    (hcases : ∀ g : G, g = 1 ∨ g = σ ∨ g = τ ∨ g = σ * τ)
    (H : Subgroup G) :
    H = ⊥ ∨ H = Subgroup.zpowers σ ∨ H = Subgroup.zpowers τ ∨
      H = Subgroup.zpowers (σ * τ) ∨ H = ⊤ := by
  classical
  by_cases hσ : σ ∈ H
  · by_cases hτ : τ ∈ H
    · right; right; right; right
      apply top_unique
      intro g _
      rcases hcases g with rfl | rfl | rfl | rfl
      · exact H.one_mem
      · exact hσ
      · exact hτ
      · exact H.mul_mem hσ hτ
    · right; left
      apply le_antisymm
      · intro g hg
        rcases hcases g with rfl | rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact ⟨1, by simp⟩
        · exact (hτ hg).elim
        · have hm := H.mul_mem hσ hg
          have heq : σ * (σ * τ) = τ := by
            rw [← mul_assoc, ← pow_two, hσsq, one_mul]
          exact (hτ (heq ▸ hm)).elim
      · exact Subgroup.zpowers_le.mpr hσ
  · by_cases hτ : τ ∈ H
    · right; right; left
      apply le_antisymm
      · intro g hg
        rcases hcases g with rfl | rfl | rfl | rfl
        · exact Subgroup.one_mem _
        · exact (hσ hg).elim
        · exact ⟨1, by simp⟩
        · have hm := H.mul_mem hg hτ
          have heq : (σ * τ) * τ = σ := by
            rw [mul_assoc, ← pow_two, hτsq, mul_one]
          exact (hσ (heq ▸ hm)).elim
      · exact Subgroup.zpowers_le.mpr hτ
    · by_cases hστ : σ * τ ∈ H
      · right; right; right; left
        apply le_antisymm
        · intro g hg
          rcases hcases g with rfl | rfl | rfl | rfl
          · exact Subgroup.one_mem _
          · exact (hσ hg).elim
          · exact (hτ hg).elim
          · exact ⟨1, by simp⟩
        · exact Subgroup.zpowers_le.mpr hστ
      · left
        apply le_antisymm
        · intro g hg
          rcases hcases g with rfl | rfl | rfl | rfl
          · exact Subgroup.mem_bot.mpr rfl
          · exact (hσ hg).elim
          · exact (hτ hg).elim
          · exact (hστ hg).elim
        · exact bot_le

/-- In a four-automorphism extension, an element fixed by exactly one of the
three nontrivial automorphisms generates the fixed field of that involution. -/
lemma apm_b93j04_fixingSubgroup_adjoin_singleton
    (F L : Type*) [Field F] [Field L] [Algebra F L] [CharZero L]
    (x : L) (γ δ ε : L ≃ₐ[F] L)
    (hx : x ≠ 0)
    (hγ : γ x = x) (hδ : δ x = -x) (hε : ε x = -x)
    (hcases : ∀ φ : L ≃ₐ[F] L, φ = 1 ∨ φ = γ ∨ φ = δ ∨ φ = ε) :
    (IntermediateField.adjoin F ({x} : Set L)).fixingSubgroup = Subgroup.zpowers γ := by
  classical
  have hfix (φ : L ≃ₐ[F] L) (hφ : φ x = x) :
      φ ∈ (IntermediateField.adjoin F ({x} : Set L)).fixingSubgroup := by
    have hxfield : x ∈ IntermediateField.fixedField (Subgroup.zpowers φ) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro f hf
      rcases hf with ⟨n, rfl⟩
      apply zpow_induction_right (P := fun e : L ≃ₐ[F] L => e x = x) rfl
      · intro a ha
        simp [ha, hφ]
      · intro a ha
        have hinv : φ⁻¹ x = x := by
          apply φ.injective
          simp [hφ]
        simp [ha, hinv]
    have hle : IntermediateField.adjoin F ({x} : Set L) ≤
        IntermediateField.fixedField (Subgroup.zpowers φ) := by
      apply IntermediateField.adjoin_le_iff.mpr
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact hxfield
    exact (IntermediateField.le_iff_le
      (K := IntermediateField.adjoin F ({x} : Set L))
      (H := Subgroup.zpowers φ)).mp hle (by exact ⟨1, by simp⟩)
  apply le_antisymm
  · intro φ hφ
    have hφx : φ x = x :=
      (IntermediateField.mem_fixingSubgroup_iff
        (K := IntermediateField.adjoin F ({x} : Set L)) φ).mp hφ x
        (IntermediateField.subset_adjoin F _ (by simp))
    rcases hcases φ with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact ⟨1, by simp⟩
    · exfalso
      rw [hδ] at hφx
      apply hx
      have htwo : (2 : L) ≠ 0 := by
        exact two_ne_zero
      have hz : (2 : L) * x = 0 := by linear_combination -hφx
      exact (mul_eq_zero.mp hz).resolve_left htwo
    · exfalso
      rw [hε] at hφx
      apply hx
      have htwo : (2 : L) ≠ 0 := two_ne_zero
      have hz : (2 : L) * x = 0 := by linear_combination -hφx
      exact (mul_eq_zero.mp hz).resolve_left htwo
  · exact Subgroup.zpowers_le.mpr (hfix γ hγ)

/-- A root of the quartic canonically yields the two radical generators. -/
lemma apm_b93j04_exists_radicals
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly] :
    ∃ r₂ r₃ : K,
      r₂ ^ 2 = algebraMap ℚ K 2 ∧ r₃ ^ 2 = algebraMap ℚ K 3 := by
  have hs := IsSplittingField.splits K apm_b93j04_poly
  have hd : (apm_b93j04_poly.map (algebraMap ℚ K)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ K).injective]
    intro h
    have hp := Polynomial.eq_C_of_degree_eq_zero h
    have hc := congrArg (fun p : Polynomial ℚ => p.coeff 4) hp
    norm_num [apm_b93j04_poly] at hc
  obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero hd
  have hx' : x ^ 4 - 10 * x ^ 2 + 1 = 0 := by
    simpa [apm_b93j04_poly] using hx
  have hxn : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx'
  have hinv : x⁻¹ = 10 * x - x ^ 3 := by
    apply (mul_eq_one_iff_inv_eq₀ hxn).mp
    calc
      x * (10 * x - x ^ 3) = 10 * x ^ 2 - x ^ 4 := by ring
      _ = 1 := by linear_combination -hx'
  have hxmul : (x ^ 4 - 10 * x ^ 2 + 1) * x ^ 2 = 0 := by rw [hx']; simp
  have htwo : (2 : K) ≠ 0 := by
    rw [show (2 : K) = algebraMap ℚ K (2 : ℚ) by norm_num]
    intro h
    have h' : algebraMap ℚ K (2 : ℚ) = algebraMap ℚ K 0 := by simpa using h
    have hh := (algebraMap ℚ K).injective h'
    norm_num at hh
  refine ⟨(x - x⁻¹) / 2, (x + x⁻¹) / 2, ?_, ?_⟩
  · rw [show algebraMap ℚ K 2 = (2 : K) by norm_num]
    rw [hinv]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero _ htwo)).2
    norm_num
    ring_nf at hxmul ⊢
    linear_combination hxmul - 8 * hx'
  · rw [show algebraMap ℚ K 3 = (3 : K) by norm_num]
    rw [hinv]
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero _ htwo)).2
    norm_num
    ring_nf at hxmul ⊢
    linear_combination hxmul - 12 * hx'

/-- Two square-root witnesses generate an arbitrary splitting field of the
quartic.  The key point is the explicit factorization into the four signed
radical roots. -/
lemma apm_b93j04_adjoin_radicals_eq_top
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) :
    IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ := by
  apply IntermediateField.adjoin_eq_top_of_algebra
  apply le_antisymm le_top
  rw [← IsSplittingField.adjoin_rootSet K apm_b93j04_poly]
  apply Algebra.adjoin_le
  intro y hy
  have hy0 : Polynomial.eval₂ (algebraMap ℚ K) y apm_b93j04_poly = 0 := by
    exact (Polynomial.mem_rootSet.mp hy).2
  have hy' : y ^ 4 - 10 * y ^ 2 + 1 = 0 := by
    simpa [apm_b93j04_poly] using hy0
  have hfac :
      (y - (r₂ + r₃)) * (y - (r₂ - r₃)) *
        (y - (-r₂ + r₃)) * (y - (-r₂ - r₃)) = 0 := by
    calc
      _ = y ^ 4 - 2 * (r₂ ^ 2 + r₃ ^ 2) * y ^ 2 +
          (r₂ ^ 2 - r₃ ^ 2) ^ 2 := by ring
      _ = 0 := by rw [h₂, h₃]; norm_num at ⊢; exact hy'
  have hr₂ : r₂ ∈ Algebra.adjoin ℚ ({r₂, r₃} : Set K) :=
    Algebra.subset_adjoin (by simp)
  have hr₃ : r₃ ∈ Algebra.adjoin ℚ ({r₂, r₃} : Set K) :=
    Algebra.subset_adjoin (by simp)
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rw [sub_eq_zero.mp h]
        exact (Algebra.adjoin ℚ ({r₂, r₃} : Set K)).add_mem hr₂ hr₃
      · rw [sub_eq_zero.mp h]
        exact (Algebra.adjoin ℚ ({r₂, r₃} : Set K)).sub_mem hr₂ hr₃
    · rw [sub_eq_zero.mp h]
      exact (Algebra.adjoin ℚ ({r₂, r₃} : Set K)).add_mem
        ((Algebra.adjoin ℚ ({r₂, r₃} : Set K)).neg_mem hr₂) hr₃
  · rw [sub_eq_zero.mp h]
    exact (Algebra.adjoin ℚ ({r₂, r₃} : Set K)).sub_mem
      ((Algebra.adjoin ℚ ({r₂, r₃} : Set K)).neg_mem hr₂) hr₃

/-- The radical witnesses can be chosen to satisfy the first three clauses of
the final theorem simultaneously. -/
lemma apm_b93j04_exists_radicals_adjoin_eq_top
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly] :
    ∃ r₂ r₃ : K,
      r₂ ^ 2 = algebraMap ℚ K 2 ∧
      r₃ ^ 2 = algebraMap ℚ K 3 ∧
      IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ := by
  obtain ⟨r₂, r₃, h₂, h₃⟩ := apm_b93j04_exists_radicals K
  exact ⟨r₂, r₃, h₂, h₃,
    apm_b93j04_adjoin_radicals_eq_top K r₂ r₃ h₂ h₃⟩

/-- The two quadratic generators give the expected upper bound on the degree
of the splitting field. -/
lemma apm_b93j04_finrank_le_four
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤) :
    Module.finrank ℚ K ≤ 4 := by
  let p₂ : Polynomial ℚ := X ^ 2 - C 2
  let p₃ : Polynomial ℚ := X ^ 2 - C 3
  have hp₂m : p₂.Monic := by exact monic_X_pow_sub_C 2 (by norm_num)
  have hp₃m : p₃.Monic := by exact monic_X_pow_sub_C 3 (by norm_num)
  have hp₂e : Polynomial.eval₂ (algebraMap ℚ K) r₂ p₂ = 0 := by
    simp [p₂]
    rw [sub_eq_zero]
    simpa using h₂
  have hp₃e : Polynomial.eval₂ (algebraMap ℚ K) r₃ p₃ = 0 := by
    simp [p₃]
    rw [sub_eq_zero]
    simpa using h₃
  have hi₂ : IsIntegral ℚ r₂ := ⟨p₂, hp₂m, hp₂e⟩
  have hi₃ : IsIntegral ℚ r₃ := ⟨p₃, hp₃m, hp₃e⟩
  have hd₂ : Module.finrank ℚ (IntermediateField.adjoin ℚ {r₂}) ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hi₂]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ r₂ hp₂e)
      hp₂m.ne_zero).trans_eq (by exact natDegree_X_pow_sub_C)
  have hd₃ : Module.finrank ℚ (IntermediateField.adjoin ℚ {r₃}) ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hi₃]
    exact (Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ r₃ hp₃e)
      hp₃m.ne_zero).trans_eq (by exact natDegree_X_pow_sub_C)
  rw [← IntermediateField.finrank_top' (F := ℚ) (E := K), ← hadj,
    show ({r₂, r₃} : Set K) = {r₂} ∪ {r₃} by ext; simp [or_comm],
    IntermediateField.adjoin_union]
  exact (IntermediateField.finrank_sup_le
    (E1 := IntermediateField.adjoin ℚ {r₂})
    (E2 := IntermediateField.adjoin ℚ {r₃})).trans
    (Nat.mul_le_mul hd₂ hd₃)

/-- The concrete rational nonsquares arising in the quartic factorization. -/
lemma apm_b93j04_rational_nonsquares :
    (∀ a : ℚ, a ^ 2 ≠ 2) ∧
    (∀ a : ℚ, a ^ 2 ≠ 3) ∧
    (∀ a : ℚ, a ^ 2 ≠ 6) ∧
    (∀ a : ℚ, a ^ 2 ≠ 8) ∧
    (∀ a : ℚ, a ^ 2 ≠ 12) ∧
    (∀ a : ℚ, a ^ 2 ≠ 24) := by
  repeat' constructor
  all_goals
    intro a h
    have hs : IsSquare (_ : ℚ) := ⟨a, by simpa [pow_two] using h.symm⟩
    norm_num at hs

/-- A square root of two in a rational extension is not already rational. -/
lemma apm_b93j04_sqrt_two_not_mem_bot
    (K : Type*) [Field K] [Algebra ℚ K] (r₂ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2) :
    r₂ ∉ (⊥ : IntermediateField ℚ K) := by
  intro hr
  rw [IntermediateField.mem_bot] at hr
  obtain ⟨a, ha⟩ := hr
  have hs : a ^ 2 = (2 : ℚ) := by
    apply (algebraMap ℚ K).injective
    simpa [← ha, map_pow] using h₂
  exact apm_b93j04_rational_nonsquares.1 a hs

/-- A square root of three in a rational extension is not already rational. -/
lemma apm_b93j04_sqrt_three_not_mem_bot
    (K : Type*) [Field K] [Algebra ℚ K] (r₃ : K)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3) :
    r₃ ∉ (⊥ : IntermediateField ℚ K) := by
  intro hr
  rw [IntermediateField.mem_bot] at hr
  obtain ⟨a, ha⟩ := hr
  have hs : a ^ 2 = (3 : ℚ) := by
    apply (algebraMap ℚ K).injective
    simpa [← ha, map_pow] using h₃
  exact apm_b93j04_rational_nonsquares.2.1 a hs

/-- The quartic admits no factorization into two monic quadratics over `ℚ`.
This is the coefficient-comparison core of its irreducibility proof. -/
lemma apm_b93j04_no_monic_quadratic_factorization
    (a b c d : ℚ) :
    (X ^ 2 + C a * X + C b) * (X ^ 2 + C c * X + C d) ≠
      apm_b93j04_poly := by
  intro h
  ring_nf at h
  have h3 := congrArg (fun p : Polynomial ℚ => p.coeff 3) h
  have h2 := congrArg (fun p : Polynomial ℚ => p.coeff 2) h
  have h1 := congrArg (fun p : Polynomial ℚ => p.coeff 1) h
  have h0 := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
  norm_num [apm_b93j04_poly] at h3 h2 h1 h0
  simp only [← C_mul, coeff_C_mul, coeff_X_pow] at h3 h2 h1
  norm_num at h3 h2 h1
  simp only [coeff_one] at h3 h2 h1
  norm_num at h3 h2 h1
  have hc : c = -a := by linarith
  subst c
  have hadb : a = 0 ∨ d = b := by
    have : a * (d - b) = 0 := by nlinarith [h1]
    rcases mul_eq_zero.mp this with ha | hdb
    · exact Or.inl ha
    · exact Or.inr (by linarith)
  rcases hadb with ha | hdb
  · subst a
    have hbquad : b ^ 2 + 10 * b + 1 = 0 := by
      linear_combination b * h2 - h0
    have hs : (b + 5) ^ 2 = 24 := by nlinarith [hbquad]
    exact apm_b93j04_rational_nonsquares.2.2.2.2.2 (b + 5) hs
  · subst d
    have hb : b = 1 ∨ b = -1 := (sq_eq_one_iff).mp (by nlinarith [h0])
    rcases hb with hb | hb
    · subst b
      exact apm_b93j04_rational_nonsquares.2.2.2.2.1 a (by nlinarith [h2])
    · subst b
      exact apm_b93j04_rational_nonsquares.2.2.2.1 a (by nlinarith [h2])

/-- The quartic has no rational root, ruling out linear factors. -/
lemma apm_b93j04_no_rational_root (a : ℚ) :
    Polynomial.eval a apm_b93j04_poly ≠ 0 := by
  intro h
  have h' : a ^ 4 - 10 * a ^ 2 + 1 = 0 := by
    simpa [apm_b93j04_poly] using h
  have hs : (a ^ 2 - 5) ^ 2 = 24 := by nlinarith [h']
  exact apm_b93j04_rational_nonsquares.2.2.2.2.2 (a ^ 2 - 5) hs

/-- Normal form for the monic quadratic divisors used in the irreducibility
argument. -/
lemma apm_b93j04_monic_quadratic_normal_form
    (q : Polynomial ℚ) (hq : q.Monic) (hd : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  have hc : q.coeff 2 = 1 := by rw [← hd]; exact hq.coeff_natDegree
  rw [q.as_sum_range_C_mul_X_pow, hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hc]
  norm_num
  ring

/-- The defining quartic is irreducible over `ℚ`. -/
lemma apm_b93j04_poly_irreducible : Irreducible apm_b93j04_poly := by
  apply (apm_b93j04_poly_monic.irreducible_iff_lt_natDegree_lt (by
    intro h
    have := congrArg (fun p : Polynomial ℚ => p.coeff 4) h
    norm_num [apm_b93j04_poly] at this)).2
  intro q hqm hqd hdiv
  rw [apm_b93j04_poly_natDegree] at hqd
  have hcases : q.natDegree = 1 ∨ q.natDegree = 2 := by
    simp only [Finset.mem_Ioc] at hqd
    omega
  rcases hcases with hq1 | hq2
  · have hdq : q.degree = 1 :=
      (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).2 hq1
    obtain ⟨x, hx⟩ := Polynomial.exists_root_of_degree_eq_one hdq
    exact apm_b93j04_no_rational_root x
      (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdiv hx)
  · obtain ⟨f, hf⟩ := hdiv
    have hfm : f.Monic := hqm.of_mul_monic_left (by rw [← hf]; exact apm_b93j04_poly_monic)
    have hf2 : f.natDegree = 2 := by
      have hdeg := hqm.natDegree_mul hfm
      rw [← hf, apm_b93j04_poly_natDegree, hq2] at hdeg
      omega
    apply apm_b93j04_no_monic_quadratic_factorization
      (q.coeff 1) (q.coeff 0) (f.coeff 1) (f.coeff 0)
    rw [← apm_b93j04_monic_quadratic_normal_form q hqm hq2,
      ← apm_b93j04_monic_quadratic_normal_form f hfm hf2, ← hf]

/-- The splitting field has degree exactly four. -/
lemma apm_b93j04_finrank_eq_four
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤) :
    Module.finrank ℚ K = 4 := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K apm_b93j04_poly
  have hle := apm_b93j04_finrank_le_four K r₂ r₃ h₂ h₃ hadj
  have hd : 4 ∣ Module.finrank ℚ K := by
    simpa [apm_b93j04_poly_natDegree] using
      apm_b93j04_poly_irreducible.natDegree_dvd_finrank
        (IsSplittingField.splits K apm_b93j04_poly)
  obtain ⟨n, hn⟩ := hd
  have hp : 0 < Module.finrank ℚ K := Module.finrank_pos
  omega

/-- The sum `r₂ + r₃` is already a primitive element: the cubic identity
recovers `r₂`, after which `r₃` is obtained by subtraction. -/
lemma apm_b93j04_adjoin_radical_sum_eq_top
    (K : Type*) [Field K] [Algebra ℚ K]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤) :
    IntermediateField.adjoin ℚ ({r₂ + r₃} : Set K) = ⊤ := by
  let E := IntermediateField.adjoin ℚ ({r₂ + r₃} : Set K)
  have hx : r₂ + r₃ ∈ E := IntermediateField.subset_adjoin ℚ _ (by simp)
  have h₂' : r₂ ^ 2 = (2 : K) := by simpa using h₂
  have h₃' : r₃ ^ 2 = (3 : K) := by simpa using h₃
  have h₂mul : r₂ ^ 3 = 2 * r₂ := by
    calc r₂ ^ 3 = r₂ ^ 2 * r₂ := by ring
         _ = 2 * r₂ := by rw [h₂']
  have h₃mul : r₃ ^ 3 = 3 * r₃ := by
    calc r₃ ^ 3 = r₃ ^ 2 * r₃ := by ring
         _ = 3 * r₃ := by rw [h₃']
  have hcubic : (r₂ + r₃) ^ 3 = 11 * r₂ + 9 * r₃ := by
    calc
      (r₂ + r₃) ^ 3 = r₂ ^ 3 + 3 * r₂ ^ 2 * r₃ +
          3 * r₂ * r₃ ^ 2 + r₃ ^ 3 := by ring
      _ = 11 * r₂ + 9 * r₃ := by rw [h₂mul, h₃mul, h₂', h₃']; ring
  have htwo : (2 : K) ≠ 0 := by
    rw [show (2 : K) = algebraMap ℚ K (2 : ℚ) by norm_num]
    intro h
    have h' : algebraMap ℚ K (2 : ℚ) = algebraMap ℚ K 0 := by simpa using h
    exact (by norm_num : (2 : ℚ) ≠ 0) ((algebraMap ℚ K).injective h')
  have hr₂formula : r₂ = ((r₂ + r₃) ^ 3 - 9 * (r₂ + r₃)) / 2 := by
    apply (eq_div_iff htwo).2
    rw [hcubic]
    ring
  have hr₂ : r₂ ∈ E := by
    rw [hr₂formula]
    exact E.div_mem
      (E.sub_mem (E.toSubalgebra.pow_mem hx 3) (E.mul_mem (E.natCast_mem 9) hx))
      (E.natCast_mem 2)
  have hr₃ : r₃ ∈ E := by
    rw [show r₃ = (r₂ + r₃) - r₂ by ring]
    exact E.sub_mem hx hr₂
  apply top_unique
  rw [← hadj]
  apply IntermediateField.adjoin_le_iff.mpr
  intro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact hr₂
  · exact hr₃

/-- The primitive radical sum supplies a power basis of the whole splitting
field. -/
noncomputable def apm_b93j04_radicalSumPowerBasis
    (K : Type*) [Field K] [Algebra ℚ K]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤) :
    PowerBasis ℚ K := by
  let x := r₂ + r₃
  have hx0 : Polynomial.eval₂ (algebraMap ℚ K) x apm_b93j04_poly = 0 :=
    apm_b93j04_radical_root K r₂ r₃ h₂ h₃
  have hi : IsIntegral ℚ x := ⟨apm_b93j04_poly, apm_b93j04_poly_monic, hx0⟩
  have hxif : IntermediateField.adjoin ℚ ({x} : Set K) = ⊤ :=
    apm_b93j04_adjoin_radical_sum_eq_top K r₂ r₃ h₂ h₃ hadj
  have hxalg : Algebra.adjoin ℚ ({x} : Set K) = ⊤ :=
    (IntermediateField.adjoin_eq_top_iff_of_isAlgebraic (by
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact hi.isAlgebraic)).mp hxif
  exact PowerBasis.ofAdjoinEqTop hi hxalg

/-- Any other root of the quartic is the image of the primitive radical sum
under a `ℚ`-automorphism.  The power-basis lift supplies the endomorphism;
finite dimensionality turns its field-homomorphism injectivity into
surjectivity. -/
lemma apm_b93j04_exists_algEquiv_map_radicalSum
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ y : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤)
    (hy : Polynomial.eval₂ (algebraMap ℚ K) y apm_b93j04_poly = 0) :
    ∃ e : K ≃ₐ[ℚ] K, e (r₂ + r₃) = y := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K apm_b93j04_poly
  let pb := apm_b93j04_radicalSumPowerBasis K r₂ r₃ h₂ h₃ hadj
  have hpgen : pb.gen = r₂ + r₃ := rfl
  have hx0 : Polynomial.eval₂ (algebraMap ℚ K) (r₂ + r₃) apm_b93j04_poly = 0 :=
    apm_b93j04_radical_root K r₂ r₃ h₂ h₃
  have hmin : minpoly ℚ pb.gen = apm_b93j04_poly := by
    rw [hpgen]
    exact (minpoly.eq_of_irreducible_of_monic apm_b93j04_poly_irreducible hx0
      apm_b93j04_poly_monic).symm
  have hymin : aeval y (minpoly ℚ pb.gen) = 0 := by
    rw [hmin]
    exact hy
  let f : K →ₐ[ℚ] K := pb.lift y hymin
  have hbij : Function.Bijective f := by
    refine ⟨f.injective, ?_⟩
    exact LinearMap.surjective_of_injective f.injective
  let e : K ≃ₐ[ℚ] K := AlgEquiv.ofBijective f hbij
  refine ⟨e, ?_⟩
  change f (r₂ + r₃) = y
  rw [← hpgen]
  exact pb.lift_gen y hymin

/-- The two independent sign changes exist as automorphisms of the abstract
splitting field. -/
lemma apm_b93j04_exists_sign_automorphisms
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤) :
    ∃ σ τ : K ≃ₐ[ℚ] K,
      σ r₂ = -r₂ ∧ σ r₃ = r₃ ∧ τ r₂ = r₂ ∧ τ r₃ = -r₃ := by
  have hroots := apm_b93j04_four_radical_roots K r₂ r₃ h₂ h₃
  obtain ⟨σ, hσsum⟩ := apm_b93j04_exists_algEquiv_map_radicalSum
    K r₂ r₃ (-r₂ + r₃) h₂ h₃ hadj hroots.2.2.1
  obtain ⟨τ, hτsum⟩ := apm_b93j04_exists_algEquiv_map_radicalSum
    K r₂ r₃ (r₂ - r₃) h₂ h₃ hadj hroots.2.1
  have h₂' : r₂ ^ 2 = (2 : K) := by simpa using h₂
  have h₃' : r₃ ^ 2 = (3 : K) := by simpa using h₃
  have htwo : (2 : K) ≠ 0 := by
    rw [show (2 : K) = algebraMap ℚ K (2 : ℚ) by norm_num]
    intro h
    have h' : algebraMap ℚ K (2 : ℚ) = algebraMap ℚ K 0 := by simpa using h
    exact (by norm_num : (2 : ℚ) ≠ 0) ((algebraMap ℚ K).injective h')
  have h₂cube : r₂ ^ 3 = 2 * r₂ := by
    calc r₂ ^ 3 = r₂ ^ 2 * r₂ := by ring
         _ = 2 * r₂ := by rw [h₂']
  have h₃cube : r₃ ^ 3 = 3 * r₃ := by
    calc r₃ ^ 3 = r₃ ^ 2 * r₃ := by ring
         _ = 3 * r₃ := by rw [h₃']
  have hpluscube : (r₂ + r₃) ^ 3 = 11 * r₂ + 9 * r₃ := by
    calc
      (r₂ + r₃) ^ 3 = r₂ ^ 3 + 3 * r₂ ^ 2 * r₃ +
          3 * r₂ * r₃ ^ 2 + r₃ ^ 3 := by ring
      _ = 11 * r₂ + 9 * r₃ := by rw [h₂cube, h₃cube, h₂', h₃']; ring
  have hsigmacube : (-r₂ + r₃) ^ 3 = -11 * r₂ + 9 * r₃ := by
    calc
      (-r₂ + r₃) ^ 3 = -(r₂ ^ 3) + 3 * r₂ ^ 2 * r₃ -
          3 * r₂ * r₃ ^ 2 + r₃ ^ 3 := by ring
      _ = -11 * r₂ + 9 * r₃ := by rw [h₂cube, h₃cube, h₂', h₃']; ring
  have htaucube : (r₂ - r₃) ^ 3 = 11 * r₂ - 9 * r₃ := by
    calc
      (r₂ - r₃) ^ 3 = r₂ ^ 3 - 3 * r₂ ^ 2 * r₃ +
          3 * r₂ * r₃ ^ 2 - r₃ ^ 3 := by ring
      _ = 11 * r₂ - 9 * r₃ := by rw [h₂cube, h₃cube, h₂', h₃']; ring
  have hr₂formula : r₂ = ((r₂ + r₃) ^ 3 - 9 * (r₂ + r₃)) / 2 := by
    apply (eq_div_iff htwo).2
    rw [hpluscube]
    ring
  have hσnine : σ (9 : K) = 9 := by
    rw [show (9 : K) = algebraMap ℚ K (9 : ℚ) by norm_num, σ.commutes]
  have hσtwo : σ (2 : K) = 2 := by
    rw [show (2 : K) = algebraMap ℚ K (2 : ℚ) by norm_num, σ.commutes]
  have hτnine : τ (9 : K) = 9 := by
    rw [show (9 : K) = algebraMap ℚ K (9 : ℚ) by norm_num, τ.commutes]
  have hτtwo : τ (2 : K) = 2 := by
    rw [show (2 : K) = algebraMap ℚ K (2 : ℚ) by norm_num, τ.commutes]
  have hσ₂ : σ r₂ = -r₂ := by
    calc
      σ r₂ = σ (((r₂ + r₃) ^ 3 - 9 * (r₂ + r₃)) / 2) := congrArg σ hr₂formula
      _ = σ ((r₂ + r₃) ^ 3 - 9 * (r₂ + r₃)) / σ 2 := map_div₀ σ _ _
      _ = ((σ (r₂ + r₃)) ^ 3 - 9 * σ (r₂ + r₃)) / 2 := by
        rw [map_sub, map_pow, map_mul, hσnine, hσtwo]
      _ = -r₂ := by rw [hσsum, hsigmacube]; apply (div_eq_iff htwo).2; ring
  have hσ₃ : σ r₃ = r₃ := by
    calc
      σ r₃ = σ ((r₂ + r₃) - r₂) := by apply congrArg σ; ring
      _ = σ (r₂ + r₃) - σ r₂ := by simp
      _ = r₃ := by rw [hσsum, hσ₂]; ring
  have hτ₂ : τ r₂ = r₂ := by
    calc
      τ r₂ = τ (((r₂ + r₃) ^ 3 - 9 * (r₂ + r₃)) / 2) := congrArg τ hr₂formula
      _ = τ ((r₂ + r₃) ^ 3 - 9 * (r₂ + r₃)) / τ 2 := map_div₀ τ _ _
      _ = ((τ (r₂ + r₃)) ^ 3 - 9 * τ (r₂ + r₃)) / 2 := by
        rw [map_sub, map_pow, map_mul, hτnine, hτtwo]
      _ = r₂ := by rw [hτsum, htaucube]; apply (div_eq_iff htwo).2; ring
  have hτ₃ : τ r₃ = -r₃ := by
    calc
      τ r₃ = τ ((r₂ + r₃) - r₂) := by apply congrArg τ; ring
      _ = τ (r₂ + r₃) - τ r₂ := by simp
      _ = -r₃ := by rw [hτsum, hτ₂]; ring
  exact ⟨σ, τ, hσ₂, hσ₃, hτ₂, hτ₃⟩

/-- Once the two sign changes are fixed, preservation of the two square
equations exhausts all automorphisms. -/
lemma apm_b93j04_automorphism_four_cases
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤)
    (σ τ : K ≃ₐ[ℚ] K)
    (hσ₂ : σ r₂ = -r₂) (hσ₃ : σ r₃ = r₃)
    (hτ₂ : τ r₂ = r₂) (hτ₃ : τ r₃ = -r₃) :
    ∀ φ : K ≃ₐ[ℚ] K, φ = 1 ∨ φ = σ ∨ φ = τ ∨ φ = σ * τ := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K apm_b93j04_poly
  letI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  have halg : Algebra.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ :=
    Algebra.adjoin_eq_top_of_intermediateField
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x)) hadj
  have hext (f g : K ≃ₐ[ℚ] K) (hr₂ : f r₂ = g r₂) (hr₃ : f r₃ = g r₃) : f = g := by
    have hhom : f.toAlgHom = g.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top halg
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hr₂
      · exact hr₃
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun q : K →ₐ[ℚ] K => q x) hhom
  intro φ
  have hφ₂sq : (φ r₂) ^ 2 = r₂ ^ 2 := by
    rw [← map_pow, h₂, φ.commutes]
  have hφ₃sq : (φ r₃) ^ 2 = r₃ ^ 2 := by
    rw [← map_pow, h₃, φ.commutes]
  rcases eq_or_eq_neg_of_sq_eq_sq (φ r₂) r₂ hφ₂sq with hφ₂ | hφ₂
  · rcases eq_or_eq_neg_of_sq_eq_sq (φ r₃) r₃ hφ₃sq with hφ₃ | hφ₃
    · exact Or.inl (hext φ 1 (by simpa using hφ₂) (by simpa using hφ₃))
    · exact Or.inr (Or.inr (Or.inl (hext φ τ (hφ₂.trans hτ₂.symm)
        (hφ₃.trans hτ₃.symm))))
  · rcases eq_or_eq_neg_of_sq_eq_sq (φ r₃) r₃ hφ₃sq with hφ₃ | hφ₃
    · exact Or.inr (Or.inl (hext φ σ (hφ₂.trans hσ₂.symm)
        (hφ₃.trans hσ₃.symm)))
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply hext φ (σ * τ)
      · simp [hφ₂, hσ₂, hτ₂]
      · simp [hφ₃, hσ₃, hτ₃]

/-- The explicit sign automorphisms give the required Klein-four
equivalence. -/
lemma apm_b93j04_kleinFour_of_sign_automorphisms
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤)
    (σ τ : K ≃ₐ[ℚ] K)
    (hσ₂ : σ r₂ = -r₂) (hσ₃ : σ r₃ = r₃)
    (hτ₂ : τ r₂ = r₂) (hτ₃ : τ r₃ = -r₃) :
    Nonempty ((K ≃ₐ[ℚ] K) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K apm_b93j04_poly
  letI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  letI : Normal ℚ K := Normal.of_isSplittingField apm_b93j04_poly
  letI : IsGalois ℚ K := ⟨⟩
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hcard : Nat.card (K ≃ₐ[ℚ] K) = 4 := by
    rw [IsGalois.card_aut_eq_finrank ℚ K]
    exact apm_b93j04_finrank_eq_four K r₂ r₃ h₂ h₃ hadj
  have halg : Algebra.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ :=
    Algebra.adjoin_eq_top_of_intermediateField
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x)) hadj
  have hext (f g : K ≃ₐ[ℚ] K) (hr₂ : f r₂ = g r₂) (hr₃ : f r₃ = g r₃) : f = g := by
    have hhom : f.toAlgHom = g.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top halg
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hr₂
      · exact hr₃
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun q : K →ₐ[ℚ] K => q x) hhom
  have hσsq : σ ^ 2 = 1 := by
    apply hext
    · simp [pow_two, hσ₂]
    · simp [pow_two, hσ₃]
  have hτsq : τ ^ 2 = 1 := by
    apply hext
    · simp [pow_two, hτ₂]
    · simp [pow_two, hτ₃]
  have hστsq : (σ * τ) ^ 2 = 1 := by
    apply hext
    · simp [pow_two, hσ₂, hτ₂]
    · simp [pow_two, hσ₃, hτ₃]
  have hcases := apm_b93j04_automorphism_four_cases
    K r₂ r₃ h₂ h₃ hadj σ τ hσ₂ hσ₃ hτ₂ hτ₃
  have hpows : ∀ φ : K ≃ₐ[ℚ] K, φ ^ 2 = 1 := by
    intro φ
    rcases hcases φ with rfl | rfl | rfl | rfl
    · simp
    · exact hσsq
    · exact hτsq
    · exact hστsq
  have hdvd : Monoid.exponent (K ≃ₐ[ℚ] K) ∣ 2 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one hpows
  have hσne : σ ≠ 1 := by
    intro hs
    have := congrArg (fun e : K ≃ₐ[ℚ] K => e r₂) hs
    simp [hσ₂] at this
    have htwo : (2 : K) ≠ 0 := by
      rw [show (2 : K) = algebraMap ℚ K (2 : ℚ) by norm_num]
      intro hzero
      have hb : algebraMap ℚ K (2 : ℚ) = algebraMap ℚ K 0 := by simpa using hzero
      have hrat := (algebraMap ℚ K).injective hb
      norm_num at hrat
    have hz : (2 : K) * r₂ = 0 := by linear_combination -this
    have hr₂zero : r₂ = 0 := (mul_eq_zero.mp hz).resolve_left htwo
    rw [hr₂zero] at h₂
    have hb : algebraMap ℚ K (0 : ℚ) = algebraMap ℚ K 2 := by simpa using h₂
    have hrat := (algebraMap ℚ K).injective hb
    norm_num at hrat
  have hexp : Monoid.exponent (K ≃ₐ[ℚ] K) = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exfalso
      apply hσne
      have hone := Monoid.pow_exponent_eq_one σ
      simpa [h] using hone
    · exact h
  exact apm_b93J04_mulEquiv_kleinFour_of_card_exponent _ hcard hexp

/-- The finite Galois correspondence, together with the explicit sign
actions, gives exactly the five intermediate fields. -/
lemma apm_b93j04_intermediateField_five_cases
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤)
    (σ τ : K ≃ₐ[ℚ] K)
    (hσ₂ : σ r₂ = -r₂) (hσ₃ : σ r₃ = r₃)
    (hτ₂ : τ r₂ = r₂) (hτ₃ : τ r₃ = -r₃) :
    ∀ E : IntermediateField ℚ K,
      E = ⊥ ∨
      E = IntermediateField.adjoin ℚ ({r₂} : Set K) ∨
      E = IntermediateField.adjoin ℚ ({r₃} : Set K) ∨
      E = IntermediateField.adjoin ℚ ({r₂ * r₃} : Set K) ∨
      E = ⊤ := by
  letI : FiniteDimensional ℚ K :=
    IsSplittingField.finiteDimensional K apm_b93j04_poly
  letI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  letI : Normal ℚ K := Normal.of_isSplittingField apm_b93j04_poly
  letI : IsGalois ℚ K := ⟨⟩
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have hcases := apm_b93j04_automorphism_four_cases
    K r₂ r₃ h₂ h₃ hadj σ τ hσ₂ hσ₃ hτ₂ hτ₃
  have hr₂ : r₂ ≠ 0 := by
    intro hz
    rw [hz] at h₂
    have hb : algebraMap ℚ K (0 : ℚ) = algebraMap ℚ K 2 := by simpa using h₂
    have := (algebraMap ℚ K).injective hb
    norm_num at this
  have hr₃ : r₃ ≠ 0 := by
    intro hz
    rw [hz] at h₃
    have hb : algebraMap ℚ K (0 : ℚ) = algebraMap ℚ K 3 := by simpa using h₃
    have := (algebraMap ℚ K).injective hb
    norm_num at this
  have hr₂r₃ : r₂ * r₃ ≠ 0 := mul_ne_zero hr₂ hr₃
  have hfix₃ : (IntermediateField.adjoin ℚ ({r₃} : Set K)).fixingSubgroup =
      Subgroup.zpowers σ := by
    apply apm_b93j04_fixingSubgroup_adjoin_singleton ℚ K r₃ σ τ (σ * τ)
      hr₃ hσ₃ hτ₃
    · simp [hσ₃, hτ₃]
    · exact hcases
  have hfix₂ : (IntermediateField.adjoin ℚ ({r₂} : Set K)).fixingSubgroup =
      Subgroup.zpowers τ := by
    apply apm_b93j04_fixingSubgroup_adjoin_singleton ℚ K r₂ τ σ (σ * τ)
      hr₂ hτ₂ hσ₂
    · simp [hσ₂, hτ₂]
    · intro φ
      rcases hcases φ with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  have hfix₂₃ : (IntermediateField.adjoin ℚ ({r₂ * r₃} : Set K)).fixingSubgroup =
      Subgroup.zpowers (σ * τ) := by
    apply apm_b93j04_fixingSubgroup_adjoin_singleton ℚ K (r₂ * r₃)
      (σ * τ) σ τ hr₂r₃
    · simp [hσ₂, hσ₃, hτ₂, hτ₃]
    · simp [hσ₂, hσ₃]
    · simp [hτ₂, hτ₃]
    · intro φ
      rcases hcases φ with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inl h)
  have halg : Algebra.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ :=
    Algebra.adjoin_eq_top_of_intermediateField
      (fun x _ ↦ (Algebra.IsAlgebraic.isAlgebraic x)) hadj
  have hext (f g : K ≃ₐ[ℚ] K) (hr₂' : f r₂ = g r₂) (hr₃' : f r₃ = g r₃) : f = g := by
    have hhom : f.toAlgHom = g.toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top halg
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hr₂'
      · exact hr₃'
    apply AlgEquiv.ext
    intro x
    exact congrArg (fun q : K →ₐ[ℚ] K => q x) hhom
  have hσsq : σ ^ 2 = 1 := by
    apply hext <;> simp [pow_two, hσ₂, hσ₃]
  have hτsq : τ ^ 2 = 1 := by
    apply hext <;> simp [pow_two, hτ₂, hτ₃]
  intro E
  let H := E.fixingSubgroup
  have hE : IntermediateField.fixedField H = E := by
    exact IsGalois.fixedField_fixingSubgroup E
  rcases apm_b93j04_subgroup_five_cases _ σ τ hσsq hτsq hcases H with
    hH | hH | hH | hH | hH
  · right; right; right; right
    calc E = IntermediateField.fixedField H := hE.symm
         _ = ⊤ := by rw [hH, IntermediateField.fixedField_bot]
  · right; right; left
    calc E = IntermediateField.fixedField H := hE.symm
         _ = IntermediateField.adjoin ℚ ({r₃} : Set K) := by
           rw [hH, ← hfix₃, IsGalois.fixedField_fixingSubgroup]
  · right; left
    calc E = IntermediateField.fixedField H := hE.symm
         _ = IntermediateField.adjoin ℚ ({r₂} : Set K) := by
           rw [hH, ← hfix₂, IsGalois.fixedField_fixingSubgroup]
  · right; right; right; left
    calc E = IntermediateField.fixedField H := hE.symm
         _ = IntermediateField.adjoin ℚ ({r₂ * r₃} : Set K) := by
           rw [hH, ← hfix₂₃, IsGalois.fixedField_fixingSubgroup]
  · left
    calc E = IntermediateField.fixedField H := hE.symm
         _ = ⊥ := by rw [hH, IsGalois.fixedField_top]

/-- The four standard biquadratic monomials form the requested ordered basis. -/
lemma apm_b93j04_exists_radical_basis
    (K : Type*) [Field K] [Algebra ℚ K]
    [IsSplittingField ℚ K apm_b93j04_poly]
    (r₂ r₃ : K)
    (h₂ : r₂ ^ 2 = algebraMap ℚ K 2)
    (h₃ : r₃ ^ 2 = algebraMap ℚ K 3)
    (hadj : IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤) :
    ∃ basis : Module.Basis (Fin 4) ℚ K,
      basis 0 = 1 ∧ basis 1 = r₂ ∧ basis 2 = r₃ ∧ basis 3 = r₂ * r₃ := by
  let x : K := r₂ + r₃
  let pb : PowerBasis ℚ K :=
    apm_b93j04_radicalSumPowerBasis K r₂ r₃ h₂ h₃ hadj
  have hx0 : Polynomial.eval₂ (algebraMap ℚ K) x apm_b93j04_poly = 0 :=
    apm_b93j04_radical_root K r₂ r₃ h₂ h₃
  have hmin : minpoly ℚ x = apm_b93j04_poly :=
    (minpoly.eq_of_irreducible_of_monic apm_b93j04_poly_irreducible hx0
      apm_b93j04_poly_monic).symm
  have hpbdim : pb.dim = 4 := by
    rw [show pb.dim = (minpoly ℚ x).natDegree by rfl, hmin,
      apm_b93j04_poly_natDegree]
  let bpow : Module.Basis (Fin 4) ℚ K := pb.basis.reindex (finCongr hpbdim)
  let v : Fin 4 → K := ![1, r₂, r₃, r₂ * r₃]
  have h₂' : r₂ ^ 2 = (2 : K) := by simpa using h₂
  have h₃' : r₃ ^ 2 = (3 : K) := by simpa using h₃
  have hx2 : x ^ 2 = 5 + 2 * (r₂ * r₃) := by
    dsimp [x]
    calc
      (r₂ + r₃) ^ 2 = r₂ ^ 2 + 2 * (r₂ * r₃) + r₃ ^ 2 := by ring
      _ = 5 + 2 * (r₂ * r₃) := by rw [h₂', h₃']; ring
  have hx3 : x ^ 3 = 11 * r₂ + 9 * r₃ := by
    dsimp [x]
    calc
      (r₂ + r₃) ^ 3 = r₂ ^ 3 + 3 * r₂ ^ 2 * r₃ +
          3 * r₂ * r₃ ^ 2 + r₃ ^ 3 := by ring
      _ = 11 * r₂ + 9 * r₃ := by
        rw [show r₂ ^ 3 = 2 * r₂ by calc
              r₂ ^ 3 = r₂ ^ 2 * r₂ := by ring
              _ = 2 * r₂ := by rw [h₂'],
            show r₃ ^ 3 = 3 * r₃ by calc
              r₃ ^ 3 = r₃ ^ 2 * r₃ := by ring
              _ = 3 * r₃ := by rw [h₃'], h₂', h₃']
        ring
  let S := Submodule.span ℚ (Set.range v)
  have hv0 : (1 : K) ∈ S := Submodule.subset_span ⟨0, by simp [v]⟩
  have hv1 : r₂ ∈ S := Submodule.subset_span ⟨1, by simp [v]⟩
  have hv2 : r₃ ∈ S := Submodule.subset_span ⟨2, by simp [v]⟩
  have hv3 : r₂ * r₃ ∈ S := Submodule.subset_span ⟨3, by simp [v]⟩
  have hpbgen : pb.gen = x := by
    change r₂ + r₃ = x
    rfl
  have hbpow_mem : ∀ i, bpow i ∈ S := by
    intro i
    fin_cases i
    · simpa [bpow, PowerBasis.basis_eq_pow] using hv0
    · simpa [bpow, PowerBasis.basis_eq_pow, hpbgen, x] using S.add_mem hv1 hv2
    · change bpow (2 : Fin 4) ∈ S
      rw [show bpow (2 : Fin 4) = x ^ 2 by simp [bpow, hpbgen]]
      rw [hx2]
      exact S.add_mem (by simpa [Algebra.smul_def] using S.smul_mem (5 : ℚ) hv0)
        (by simpa [Algebra.smul_def] using S.smul_mem (2 : ℚ) hv3)
    · change bpow (3 : Fin 4) ∈ S
      rw [show bpow (3 : Fin 4) = x ^ 3 by simp [bpow, hpbgen]]
      rw [hx3]
      exact S.add_mem (by simpa [Algebra.smul_def] using S.smul_mem (11 : ℚ) hv1)
        (by simpa [Algebra.smul_def] using S.smul_mem (9 : ℚ) hv2)
  have hspan : (⊤ : Submodule ℚ K) ≤ Submodule.span ℚ (Set.range v) := by
    rw [← bpow.span_eq]
    exact Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; exact hbpow_mem i)
  let basis := basisOfTopLeSpanOfCardEqFinrank v hspan (by
    haveI : FiniteDimensional ℚ K := IsSplittingField.finiteDimensional K apm_b93j04_poly
    rw [Fintype.card_fin, apm_b93j04_finrank_eq_four K r₂ r₃ h₂ h₃ hadj])
  refine ⟨basis, ?_⟩
  change basis 0 = 1 ∧ basis 1 = r₂ ∧ basis 2 = r₃ ∧ basis 3 = r₂ * r₃
  simp [basis, v]

theorem apm_b93j04 :
    ∀ (K : Type*) [Field K] [Algebra ℚ K]
        [IsSplittingField ℚ K apm_b93j04_poly],
      ∃ (r₂ r₃ : K) (basis : Module.Basis (Fin 4) ℚ K)
          (σ τ : K ≃ₐ[ℚ] K),
        r₂ ^ 2 = algebraMap ℚ K 2 ∧
        r₃ ^ 2 = algebraMap ℚ K 3 ∧
        IntermediateField.adjoin ℚ ({r₂, r₃} : Set K) = ⊤ ∧
        basis 0 = 1 ∧ basis 1 = r₂ ∧ basis 2 = r₃ ∧ basis 3 = r₂ * r₃ ∧
        Nonempty ((K ≃ₐ[ℚ] K) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) ∧
        σ r₂ = -r₂ ∧ σ r₃ = r₃ ∧
        τ r₂ = r₂ ∧ τ r₃ = -r₃ ∧
        (∀ φ : K ≃ₐ[ℚ] K, φ = 1 ∨ φ = σ ∨ φ = τ ∨ φ = σ * τ) ∧
        (∀ E : IntermediateField ℚ K,
          E = ⊥ ∨
          E = IntermediateField.adjoin ℚ ({r₂} : Set K) ∨
          E = IntermediateField.adjoin ℚ ({r₃} : Set K) ∨
          E = IntermediateField.adjoin ℚ ({r₂ * r₃} : Set K) ∨
          E = ⊤) := by
  /- PARTIAL boundary (closer hop 2):
     `apm_b93J04_mulEquiv_kleinFour_of_card_exponent` now closes the abstract
     group-classification tail: once the automorphism group is shown to have
     cardinality four and exponent two, the exact frozen product equivalence
     follows from `IsKleinFour.nonempty_mulEquiv`.

     The earlier pass's `apm_b93j04_radical_root` formally verifies the
     core radical identity: whenever `r₂² = 2` and `r₃² = 3`, `r₂ + r₃` is
     a root of the frozen quartic (and sign variants follow identically).

     Closer hop 2 now compiles those sign variants explicitly as
     `apm_b93j04_four_radical_roots`, giving the complete four-element
     candidate root list required by the splitting-field argument. A search
     for multiquadratic/biquadratic extensions, adjoining square roots, and
     quadratic tower bases found no packaged construction connecting an
     arbitrary `IsSplittingField` instance to these radical witnesses.
     `Polynomial.card_rootSet_eq_natDegree` and `ncard_rootSet_le` do provide
     a viable exhaustion step after distinctness and separability are supplied;
     they do not produce the radical witnesses in the reverse direction.

     I exhaustively searched the splitting-field API, notably
     `IsSplittingField.adjoin_rootSet`, `IsSplittingField.splits`,
     `IntermediateField.adjoin_rootSet_isSplittingField`, and the finite
     Galois correspondence (`IsGalois.intermediateFieldEquivSubgroup`).
     The new helper confirms that no additional explicit equivalence
     construction is needed after cardinality four and exponent two.

     The remaining blocker is the abstraction bridge from an arbitrary
     `IsSplittingField` instance: construct square-root witnesses from its
     root set, prove the four compiled candidate roots are distinct and exhaust
     the root set, establish their linear independence and hence the displayed basis,
     then bundle the two independent sign-change automorphisms.  Only after
     that can the Galois correspondence and the five-subgroup classification
     identify every intermediate field.  No Mathlib theorem or closed sibling
     packages this polynomial-specific realization.

     CLOSER HOP 3: `apm_b93j04_four_radical_roots_pairwise` now proves all six
     pairwise inequalities among the four compiled radical candidates. The
     proof first derives `r₂ ≠ 0`, `r₃ ≠ 0`, `r₂ ≠ r₃`, and `r₂ ≠ -r₃` from
     the two square equations using injectivity of `algebraMap ℚ K`, then
     reduces every candidate equality to one of those contradictions. Hence,
     once radical witnesses are extracted, the quartic already has four
     distinct exhibited roots; the earlier distinctness/separability gap is
     closed and degree-four root bounds can supply exhaustion.

     Searches beyond hop 2 covered root-set cardinality/exhaustion, splitting-
     field root extraction, quadratic/Kummer extension construction, and
     closed neighboring Galois artifacts. They provided no reverse theorem
     extracting `√2` and `√3` from this abstract quartic splitting field. That
     extraction remains the upstream blocker, followed by the basis,
     sign-change automorphisms, and intermediate-field classification. -/
  intro K _ _ _
  obtain ⟨r₂, r₃, h₂, h₃, hadj⟩ :=
    apm_b93j04_exists_radicals_adjoin_eq_top K
  obtain ⟨basis, hb0, hb1, hb2, hb3⟩ :=
    apm_b93j04_exists_radical_basis K r₂ r₃ h₂ h₃ hadj
  obtain ⟨σ, τ, hσ₂, hσ₃, hτ₂, hτ₃⟩ :=
    apm_b93j04_exists_sign_automorphisms K r₂ r₃ h₂ h₃ hadj
  have hklein := apm_b93j04_kleinFour_of_sign_automorphisms
    K r₂ r₃ h₂ h₃ hadj σ τ hσ₂ hσ₃ hτ₂ hτ₃
  have hcases := apm_b93j04_automorphism_four_cases
    K r₂ r₃ h₂ h₃ hadj σ τ hσ₂ hσ₃ hτ₂ hτ₃
  have hfields := apm_b93j04_intermediateField_five_cases
    K r₂ r₃ h₂ h₃ hadj σ τ hσ₂ hσ₃ hτ₂ hτ₃
  exact ⟨r₂, r₃, basis, σ, τ, h₂, h₃, hadj,
    hb0, hb1, hb2, hb3, hklein, hσ₂, hσ₃, hτ₂, hτ₃, hcases, hfields⟩
