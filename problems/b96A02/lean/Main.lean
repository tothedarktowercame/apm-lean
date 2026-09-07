import Mathlib

open Polynomial
open scoped Pointwise

noncomputable section

/-!
# APM b96A02

## Statement repairs

None.

## Encoding notes

The core is Mathlib's `Subgroup.normalCore`. Splitting fields, minimal
polynomials, Galois groups, and polynomial degrees are all represented directly.
-/

lemma apm_b96a02_normal_of_card_fifteen
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30)
    (H : Subgroup G) (hH : Nat.card H = 15) : H.Normal := by
  have hm := H.card_mul_index
  rw [hH, Nat.card_eq_fintype_card, hG] at hm
  apply H.normal_of_index_eq_two
  omega

/-- The normal core of a prime-order subgroup is either trivial or the entire
subgroup. -/
lemma apm_b96a02_normalCore_eq_bot_or_eq_self_of_prime_card
    (G : Type*) [Group G] (H : Subgroup G)
    (hprime : (Nat.card H).Prime) :
    H.normalCore = ⊥ ∨ H.normalCore = H := by
  letI : Fact (Nat.card H).Prime := ⟨hprime⟩
  rcases (H.normalCore.subgroupOf H).eq_bot_or_eq_top_of_prime_card with hk | hk
  · left
    rw [Subgroup.subgroupOf_eq_bot] at hk
    apply le_antisymm
    · intro x hx
      exact Disjoint.le_bot hk ⟨hx, H.normalCore_le hx⟩
    · exact bot_le
  · right
    apply le_antisymm H.normalCore_le
    exact Subgroup.subgroupOf_eq_top.mp hk

/-- Under the finite Galois correspondence, taking the normal closure of an
intermediate field corresponds to taking the normal core of its fixing
subgroup. -/
lemma apm_b96a02_fixingSubgroup_normalClosure
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (K : IntermediateField F L) :
    (IntermediateField.normalClosure F K L).fixingSubgroup =
      K.fixingSubgroup.normalCore := by
  apply le_antisymm
  · apply Subgroup.normal_le_normalCore.mpr
    exact IntermediateField.fixingSubgroup_antitone
      (IntermediateField.le_normalClosure K)
  · apply (IntermediateField.le_iff_le _ _).mp
    apply (IntermediateField.normalClosure_le_iff_of_normal).mpr
    exact (IntermediateField.le_iff_le _ _).mpr K.fixingSubgroup.normalCore_le

lemma apm_b96a02_normalClosure_adjoin_simple
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (α : L) :
    IntermediateField.normalClosure F (IntermediateField.adjoin F {α}) L =
      IntermediateField.adjoin F ((minpoly F α).rootSet L) := by
  let K := IntermediateField.adjoin F ({α} : Set L)
  let R := IntermediateField.adjoin F ((minpoly F α).rootSet L)
  have hsplitsL : ((minpoly F α).map (algebraMap F L)).Splits := IsGalois.splits F α
  haveI : (minpoly F α).IsSplittingField F R :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplitsL
  letI : Normal F R := Normal.of_isSplittingField (minpoly F α)
  apply le_antisymm
  · apply (IntermediateField.normalClosure_le_iff_of_normal).mpr
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    have hx' : x = α := Set.mem_singleton_iff.mp hx
    subst x
    exact IntermediateField.subset_adjoin F _ <|
      Polynomial.mem_rootSet.mpr ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral α),
        minpoly.aeval F α⟩
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    have hαK : α ∈ K := IntermediateField.subset_adjoin F {α} (Set.mem_singleton α)
    have hαN : α ∈ IntermediateField.normalClosure F K L :=
      IntermediateField.le_normalClosure K hαK
    let β : IntermediateField.normalClosure F K L := ⟨α, hαN⟩
    have hsplitsN : ((minpoly F β).map
        (algebraMap F (IntermediateField.normalClosure F K L))).Splits :=
      (inferInstance : Normal F (IntermediateField.normalClosure F K L)).splits β
    have hmin : minpoly F β = minpoly F α := by
      exact (minpoly.algHom_eq (IntermediateField.normalClosure F K L).val
        (IntermediateField.normalClosure F K L).val.injective β).symm
    rw [hmin] at hsplitsN
    exact (IntermediateField.splits_iff_mem hsplitsL).mp hsplitsN x hx

lemma apm_b96a02_splitting_iff_normalCore
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (α : L) :
    (minpoly F α).IsSplittingField F L ↔
      (IntermediateField.adjoin F {α}).fixingSubgroup.normalCore = ⊥ := by
  have hsplits : ((minpoly F α).map (algebraMap F L)).Splits := IsGalois.splits F α
  rw [isSplittingField_iff_intermediateField]
  simp only [hsplits, true_and]
  rw [← apm_b96a02_normalClosure_adjoin_simple F L α]
  rw [← apm_b96a02_fixingSubgroup_normalClosure F L
    (IntermediateField.adjoin F {α})]
  constructor
  · intro h
    rw [h, IntermediateField.fixingSubgroup_top]
  · intro h
    apply (IsGalois.intermediateFieldEquivSubgroup :
      IntermediateField F L ≃o (Subgroup (L ≃ₐ[F] L))ᵒᵈ).injective
    exact h.trans IntermediateField.fixingSubgroup_top.symm

lemma apm_b96a02_degree_of_small_subgroups_normal
    (F L : Type*) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L] (α : L)
    (hcard : Nat.card (L ≃ₐ[F] L) = 30)
    (hnormal : ∀ H : Subgroup (L ≃ₐ[F] L),
      Nat.card H = 3 ∨ Nat.card H = 5 → H.Normal)
    (hsplit : (minpoly F α).IsSplittingField F L) :
    (minpoly F α).natDegree = 15 ∨ (minpoly F α).natDegree = 30 := by
  let E := IntermediateField.adjoin F ({α} : Set L)
  let H := E.fixingSubgroup
  have hcore : H.normalCore = ⊥ :=
    (apm_b96a02_splitting_iff_normalCore F L α).mp hsplit
  have hnotdvd (p : ℕ) (hp : p = 3 ∨ p = 5) : ¬ p ∣ Nat.card H := by
    intro hdvd
    haveI : Fact p.Prime := ⟨hp.elim (fun h => h ▸ by norm_num) (fun h => h ▸ by norm_num)⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    let P : Subgroup (L ≃ₐ[F] L) := Subgroup.zpowers (x : L ≃ₐ[F] L)
    have hPcard : Nat.card P = p :=
      (Nat.card_zpowers (x : L ≃ₐ[F] L)).trans (Subgroup.orderOf_coe x |>.trans hx)
    have hPnormal : P.Normal := by
      apply hnormal P
      rcases hp with rfl | rfl
      · exact Or.inl hPcard
      · exact Or.inr hPcard
    have hPle : P ≤ H := Subgroup.zpowers_le.mpr x.property
    have hPcore : P ≤ H.normalCore :=
      Subgroup.normal_le_normalCore.mpr hPle
    rw [hcore] at hPcore
    have hPbot : P = ⊥ := eq_bot_iff.mpr hPcore
    have : p = 1 := hPcard.symm.trans (hPbot ▸ Subgroup.card_bot)
    omega
  have hndvd3 : ¬ 3 ∣ Nat.card H := hnotdvd 3 (Or.inl rfl)
  have hndvd5 : ¬ 5 ∣ Nat.card H := hnotdvd 5 (Or.inr rfl)
  have hdvd30 : Nat.card H ∣ 30 := hcard ▸ Subgroup.card_subgroup_dvd_card H
  have hle : Nat.card H ≤ 30 := Nat.le_of_dvd (by omega) hdvd30
  have hHcases : Nat.card H = 1 ∨ Nat.card H = 2 := by
    have hc3 : (Nat.card H).Coprime 3 :=
      ((Nat.prime_three.coprime_iff_not_dvd.mpr hndvd3).symm)
    have hc5 : (Nat.card H).Coprime 5 :=
      (((by norm_num : Nat.Prime 5).coprime_iff_not_dvd.mpr hndvd5).symm)
    have hdvd10 : Nat.card H ∣ 10 := hc3.dvd_of_dvd_mul_left (by
      norm_num at hdvd30 ⊢
      exact hdvd30)
    have hdvd2 : Nat.card H ∣ 2 := hc5.dvd_of_dvd_mul_left (by
      norm_num at hdvd10 ⊢
      exact hdvd10)
    exact (Nat.dvd_prime (by norm_num)).mp hdvd2
  have htower := Module.finrank_mul_finrank F E L
  rw [IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral α),
    ← IsGalois.card_fixingSubgroup_eq_finrank E,
    ← IsGalois.card_aut_eq_finrank F L, hcard] at htower
  rcases hHcases with hH | hH <;> rw [hH] at htower <;> omega

lemma apm_b96a02_squarefree_thirty : Squarefree 30 := by
  rw [show 30 = 6 * 5 by norm_num, Nat.squarefree_mul (by norm_num)]
  constructor
  · rw [show 6 = 2 * 3 by norm_num, Nat.squarefree_mul (by norm_num)]
    exact ⟨Nat.prime_two.squarefree, (by norm_num : Nat.Prime 3).squarefree⟩
  · exact (by norm_num : Nat.Prime 5).squarefree

lemma apm_b96a02_three_pow_factorization_thirty :
    3 ^ (Nat.factorization 30) 3 = 3 := by
  rw [Nat.factorization_eq_one_of_squarefree apm_b96a02_squarefree_thirty
    (by norm_num) (by norm_num)]
  norm_num

lemma apm_b96a02_five_pow_factorization_thirty :
    5 ^ (Nat.factorization 30) 5 = 5 := by
  rw [Nat.factorization_eq_one_of_squarefree apm_b96a02_squarefree_thirty
    (by norm_num) (by norm_num)]
  norm_num

lemma apm_b96a02_card_sylow_three
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 10 := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let P : Sylow 3 G := default
  have hPcard : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_three_pow_factorization_thirty
  have hindex : P.index = 10 := by
    have hm := P.card_mul_index
    rw [hPcard, Nat.card_eq_fintype_card, hG] at hm
    omega
  have hdvd : Nat.card (Sylow 3 G) ∣ 10 := hindex ▸ P.card_dvd_index
  have hmod := card_sylow_modEq_one 3 G
  have hle : Nat.card (Sylow 3 G) ≤ 10 := Nat.le_of_dvd (by omega) hdvd
  interval_cases h : Nat.card (Sylow 3 G)
  all_goals solve | omega | norm_num [Nat.ModEq] at hmod

lemma apm_b96a02_card_sylow_five
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30) :
    Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 G := default
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_five_pow_factorization_thirty
  have hindex : P.index = 6 := by
    have hm := P.card_mul_index
    rw [hPcard, Nat.card_eq_fintype_card, hG] at hm
    omega
  have hdvd : Nat.card (Sylow 5 G) ∣ 6 := hindex ▸ P.card_dvd_index
  have hmod := card_sylow_modEq_one 5 G
  have hle : Nat.card (Sylow 5 G) ≤ 6 := Nat.le_of_dvd (by omega) hdvd
  interval_cases h : Nat.card (Sylow 5 G)
  all_goals solve | omega | norm_num [Nat.ModEq] at hmod

lemma apm_b96a02_normal_of_card_prime_of_unique_sylow
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hunique : Nat.card (Sylow p G) = 1)
    (hSylowCard : ∀ P : Sylow p G, Nat.card P = p)
    (H : Subgroup G) (hH : Nat.card H = p) : H.Normal := by
  letI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hunique).1
  have hHp : IsPGroup p H := IsPGroup.of_card (hH.trans (pow_one p).symm)
  obtain ⟨P, hHP⟩ := hHp.exists_le_sylow
  have hEq : H = (P : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hHP (by rw [hSylowCard P, hH])
  rw [hEq]
  exact P.normal_of_subsingleton

lemma apm_b96a02_normal_of_card_three_of_unique_sylow
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30)
    (hunique : Nat.card (Sylow 3 G) = 1)
    (H : Subgroup G) (hH : Nat.card H = 3) : H.Normal := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply apm_b96a02_normal_of_card_prime_of_unique_sylow G 3 hunique
  · intro P
    rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_three_pow_factorization_thirty
  · exact hH

lemma apm_b96a02_normal_of_card_five_of_unique_sylow
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30)
    (hunique : Nat.card (Sylow 5 G) = 1)
    (H : Subgroup G) (hH : Nat.card H = 5) : H.Normal := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply apm_b96a02_normal_of_card_prime_of_unique_sylow G 5 hunique
  · intro P
    rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_five_pow_factorization_thirty
  · exact hH

lemma apm_b96a02_le_centralizer_of_normal_cyclic_of_coprime_aut_card
    (G : Type*) [Group G] [Finite G] (P K : Subgroup G) [P.Normal] [IsCyclic P]
    (hcop : (Nat.card K).Coprime (Nat.card (MulAut P))) :
    K ≤ Subgroup.centralizer (P : Set G) := by
  have hKP : K ≤ Subgroup.normalizer (P : Subgroup G) := by
    rw [P.normalizer_eq_top]
    exact le_top
  let f : K →* MulAut P := P.normalizerMonoidHom.comp (Subgroup.inclusion hKP)
  have hrange : Nat.card f.range = 1 := Nat.eq_one_of_dvd_coprimes hcop
    (Subgroup.card_range_dvd f) f.range.card_subgroup_dvd_card
  have hrange_bot : f.range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact Subtype.ext_iff.mp <|
      (Nat.card_eq_one_iff_unique.mp hrange).1.elim (⟨x, hx⟩ : f.range) 1
  have hf : f = 1 := MonoidHom.range_eq_bot_iff.mp hrange_bot
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro p hp
  have happ := congrArg (fun g : K →* MulAut P => g ⟨k, hk⟩) hf
  have happ' := congrArg (fun a : MulAut P => a ⟨p, hp⟩) happ
  have happ'' := congrArg Subtype.val happ'
  change k * p * k⁻¹ = p at happ''
  calc
    p * k = (k * p * k⁻¹) * k := congrArg (· * k) happ''.symm
    _ = k * p := by group

lemma apm_b96a02_unique_three_forces_unique_five
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30)
    (h3 : Nat.card (Sylow 3 G) = 1) : Nat.card (Sylow 5 G) = 1 := by
  rcases apm_b96a02_card_sylow_five G hG with h5 | h5
  · exact h5
  · letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    let P3 : Sylow 3 G := default
    let P5 : Sylow 5 G := default
    have hP3card : Nat.card P3 = 3 := by
      rw [P3.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
      exact apm_b96a02_three_pow_factorization_thirty
    have hP5card : Nat.card P5 = 5 := by
      rw [P5.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
      exact apm_b96a02_five_pow_factorization_thirty
    haveI : (P3 : Subgroup G).Normal := by
      letI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h3).1
      exact P3.normal_of_subsingleton
    letI : IsCyclic P3 := isCyclic_of_prime_card hP3card
    have hcent : (P5 : Subgroup G) ≤ Subgroup.centralizer (P3 : Set G) := by
      apply apm_b96a02_le_centralizer_of_normal_cyclic_of_coprime_aut_card G P3 P5
      rw [hP5card, IsCyclic.card_mulAut P3, hP3card]
      decide
    have hcent' : (P3 : Subgroup G) ≤ Subgroup.centralizer (P5 : Set G) :=
      Subgroup.le_centralizer_iff.mp hcent
    have hle : (P3 : Subgroup G) ≤ Subgroup.normalizer (P5 : Subgroup G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hc := Subgroup.mem_centralizer_iff.mp (hcent' hg) x hx
        have heq : g * x * g⁻¹ = x := by rw [← hc]; group
        rwa [heq]
      · intro hx
        have hc := Subgroup.mem_centralizer_iff.mp (hcent' hg)
          (g * x * g⁻¹) hx
        have heq : g * x * g⁻¹ = x := by
          symm
          calc
            x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * (g * (g * x * g⁻¹)) := by
              simpa [mul_assoc] using congrArg (g⁻¹ * ·) hc
            _ = g * x * g⁻¹ := by group
        rwa [heq] at hx
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hP3card] at hdvd
    let N5 := Subgroup.normalizer ((P5 : Subgroup G) : Set G)
    have hdvdN : 3 ∣ Nat.card N5 := by simpa [N5] using hdvd
    have hindex : N5.index = 6 := by
      change (Subgroup.normalizer ((P5 : Subgroup G) : Set G)).index = 6
      rw [← P5.card_eq_index_normalizer]
      exact h5
    have hm := N5.card_mul_index
    have hGnat : Nat.card G = 30 := by simpa [Nat.card_eq_fintype_card] using hG
    rw [hindex, hGnat] at hm
    omega

lemma apm_b96a02_unique_five_forces_unique_three
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30)
    (h5 : Nat.card (Sylow 5 G) = 1) : Nat.card (Sylow 3 G) = 1 := by
  rcases apm_b96a02_card_sylow_three G hG with h3 | h3
  · exact h3
  · letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    let P3 : Sylow 3 G := default
    let P5 : Sylow 5 G := default
    have hP3card : Nat.card P3 = 3 := by
      rw [P3.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
      exact apm_b96a02_three_pow_factorization_thirty
    have hP5card : Nat.card P5 = 5 := by
      rw [P5.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
      exact apm_b96a02_five_pow_factorization_thirty
    haveI : (P5 : Subgroup G).Normal := by
      letI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h5).1
      exact P5.normal_of_subsingleton
    letI : IsCyclic P5 := isCyclic_of_prime_card hP5card
    have hcent : (P3 : Subgroup G) ≤ Subgroup.centralizer (P5 : Set G) := by
      apply apm_b96a02_le_centralizer_of_normal_cyclic_of_coprime_aut_card G P5 P3
      rw [hP3card, IsCyclic.card_mulAut P5, hP5card]
      decide
    have hcent' : (P5 : Subgroup G) ≤ Subgroup.centralizer (P3 : Set G) :=
      Subgroup.le_centralizer_iff.mp hcent
    have hle : (P5 : Subgroup G) ≤ Subgroup.normalizer (P3 : Subgroup G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hc := Subgroup.mem_centralizer_iff.mp (hcent' hg) x hx
        have heq : g * x * g⁻¹ = x := by rw [← hc]; group
        rwa [heq]
      · intro hx
        have hc := Subgroup.mem_centralizer_iff.mp (hcent' hg)
          (g * x * g⁻¹) hx
        have heq : g * x * g⁻¹ = x := by
          symm
          calc
            x = g⁻¹ * (g * x * g⁻¹) * g := by group
            _ = g⁻¹ * (g * (g * x * g⁻¹)) := by
              simpa [mul_assoc] using congrArg (g⁻¹ * ·) hc
            _ = g * x * g⁻¹ := by group
        rwa [heq] at hx
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [hP5card] at hdvd
    let N3 := Subgroup.normalizer ((P3 : Subgroup G) : Set G)
    have hdvdN : 5 ∣ Nat.card N3 := by simpa [N3] using hdvd
    have hindex : N3.index = 10 := by
      change (Subgroup.normalizer ((P3 : Subgroup G) : Set G)).index = 10
      rw [← P3.card_eq_index_normalizer]
      exact h3
    have hm := N3.card_mul_index
    have hGnat : Nat.card G = 30 := by simpa [Nat.card_eq_fintype_card] using hG
    rw [hindex, hGnat] at hm
    omega

lemma apm_b96a02_sylow_nonidentity_injective
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hcard : ∀ P : Sylow p G, Nat.card P = p) :
    Function.Injective (fun z : Σ P : Sylow p G,
      {x : (P : Subgroup G) // x ≠ 1} => (z.2.1 : G)) := by
  rintro ⟨P, x⟩ ⟨Q, y⟩ hxy
  change (x.1 : G) = (y.1 : G) at hxy
  have hxQ : (x.1 : G) ∈ (Q : Subgroup G) := by
    rw [hxy]
    exact y.1.2
  let I : Subgroup P := ((P : Subgroup G) ⊓ (Q : Subgroup G)).subgroupOf P
  have hI : I = ⊥ ∨ I = ⊤ := by
    letI : Fact (Nat.card P).Prime := ⟨by
      have hp : p.Prime := Fact.out
      simpa [hcard P] using hp⟩
    exact I.eq_bot_or_eq_top_of_prime_card
  have hPQ : P = Q := by
    rcases hI with hI | hI
    · have hz : x.1 ∈ (⊥ : Subgroup P) := by
        rw [← hI]
        exact ⟨x.1.2, hxQ⟩
      exfalso
      apply x.2
      simpa using hz
    · apply Sylow.ext
      exact (P.3 Q.2 <|
        Subgroup.subgroupOf_eq_top.mp hI |>.trans inf_le_right).symm
  subst Q
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact hxy

lemma apm_b96a02_card_sylow_nonidentity_sigma
    (G : Type*) [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (hSylowCard : ∀ P : Sylow p G, Nat.card P = p) :
    Nat.card (Σ P : Sylow p G, {x : (P : Subgroup G) // x ≠ 1}) =
      Nat.card (Sylow p G) * (p - 1) := by
  classical
  rw [Nat.card_sigma]
  have hfiber (P : Sylow p G) :
      Nat.card {x : (P : Subgroup G) // x ≠ 1} = p - 1 := by
    letI : Fintype (P : Subgroup G) := Fintype.ofFinite (P : Subgroup G)
    have hc : Nat.card (P : Subgroup G) = p := hSylowCard P
    rw [Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl (fun x : (P : Subgroup G) => x = 1)]
    simp only [Fintype.card_unique]
    rw [← Nat.card_eq_fintype_card, hc]
  simp_rw [hfiber]
  simp [← Nat.card_eq_fintype_card]

lemma apm_b96a02_one_odd_sylow_unique
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 5 G) = 1 := by
  rcases apm_b96a02_card_sylow_three G hG with h3 | h3
  · exact Or.inl h3
  rcases apm_b96a02_card_sylow_five G hG with h5 | h5
  · exact Or.inr h5
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let D3 := Σ P : Sylow 3 G, {x : (P : Subgroup G) // x ≠ 1}
  let D5 := Σ P : Sylow 5 G, {x : (P : Subgroup G) // x ≠ 1}
  let f : D3 ⊕ D5 → G
    | Sum.inl z => z.2.1
    | Sum.inr z => z.2.1
  have hP3card (P : Sylow 3 G) : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_three_pow_factorization_thirty
  have hP5card (P : Sylow 5 G) : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_five_pow_factorization_thirty
  have hinj : Function.Injective f := by
    intro x y hxy
    rcases x with x | x <;> rcases y with y | y
    · congr 1
      exact apm_b96a02_sylow_nonidentity_injective G 3 hP3card hxy
    · exfalso
      change (x.2.1 : G) = (y.2.1 : G) at hxy
      have hi : ((x.1 : Subgroup G) ⊓ (y.1 : Subgroup G)) = ⊥ :=
        Subgroup.inf_eq_bot_of_coprime (by rw [hP3card x.1, hP5card y.1]; norm_num)
      have hxbot : (x.2.1 : G) ∈ (⊥ : Subgroup G) := by
        rw [← hi]
        exact ⟨x.2.1.2, hxy ▸ y.2.1.2⟩
      apply x.2.2
      apply Subtype.ext
      simpa using hxbot
    · exfalso
      change (x.2.1 : G) = (y.2.1 : G) at hxy
      have hi : ((x.1 : Subgroup G) ⊓ (y.1 : Subgroup G)) = ⊥ :=
        Subgroup.inf_eq_bot_of_coprime (by rw [hP5card x.1, hP3card y.1]; norm_num)
      have hxbot : (x.2.1 : G) ∈ (⊥ : Subgroup G) := by
        rw [← hi]
        exact ⟨x.2.1.2, hxy ▸ y.2.1.2⟩
      apply x.2.2
      apply Subtype.ext
      simpa using hxbot
    · congr 1
      exact apm_b96a02_sylow_nonidentity_injective G 5 hP5card hxy
  have hD3 : Nat.card D3 = 20 := by
    change Nat.card (Σ P : Sylow 3 G, {x : (P : Subgroup G) // x ≠ 1}) = 20
    rw [apm_b96a02_card_sylow_nonidentity_sigma G 3 hP3card, h3]
  have hD5 : Nat.card D5 = 24 := by
    change Nat.card (Σ P : Sylow 5 G, {x : (P : Subgroup G) // x ≠ 1}) = 24
    rw [apm_b96a02_card_sylow_nonidentity_sigma G 5 hP5card, h5]
  have hle := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_sum, hD3, hD5, Nat.card_eq_fintype_card, hG] at hle
  omega

lemma apm_b96a02_order_thirty_group
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 30) :
    (∃ N : Subgroup G, N.Normal ∧ Nat.card N = 15) ∧
      (∀ H : Subgroup G,
        Nat.card H = 3 ∨ Nat.card H = 5 ∨ Nat.card H = 15 → H.Normal) := by
  have h3 : Nat.card (Sylow 3 G) = 1 := by
    rcases apm_b96a02_one_odd_sylow_unique G hG with h3 | h5
    · exact h3
    · exact apm_b96a02_unique_five_forces_unique_three G hG h5
  have h5 : Nat.card (Sylow 5 G) = 1 :=
    apm_b96a02_unique_three_forces_unique_five G hG h3
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P3 : Sylow 3 G := default
  let P5 : Sylow 5 G := default
  have hP3card : Nat.card P3 = 3 := by
    rw [P3.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_three_pow_factorization_thirty
  have hP5card : Nat.card P5 = 5 := by
    rw [P5.card_eq_multiplicity, Nat.card_eq_fintype_card, hG]
    exact apm_b96a02_five_pow_factorization_thirty
  haveI : (P3 : Subgroup G).Normal := by
    letI : Subsingleton (Sylow 3 G) := (Nat.card_eq_one_iff_unique.mp h3).1
    exact P3.normal_of_subsingleton
  haveI : (P5 : Subgroup G).Normal := by
    letI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp h5).1
    exact P5.normal_of_subsingleton
  let N : Subgroup G := (P3 : Subgroup G) ⊔ (P5 : Subgroup G)
  have hNcard : Nat.card N = 15 := by
    let mulTo : P3 × P5 → N := fun z =>
      ⟨(z.1 : G) * (z.2 : G), N.mul_mem
        ((show (P3 : Subgroup G) ≤ N from le_sup_left) z.1.2)
        ((show (P5 : Subgroup G) ≤ N from le_sup_right) z.2.2)⟩
    have hsurj : Function.Surjective mulTo := by
      intro z
      have hz : (z : G) ∈ (↑((P3 : Subgroup G) ⊔ (P5 : Subgroup G)) : Set G) := z.2
      rw [Subgroup.normal_mul (P3 : Subgroup G) (P5 : Subgroup G)] at hz
      rcases hz with ⟨a, ha, b, hb, hab⟩
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
    have hle : Nat.card N ≤ 15 := by
      have := Nat.card_le_card_of_surjective mulTo hsurj
      rw [Nat.card_prod, hP3card, hP5card] at this
      omega
    have hdvd3 : 3 ∣ Nat.card N := hP3card ▸ Subgroup.card_dvd_of_le le_sup_left
    have hdvd5 : 5 ∣ Nat.card N := hP5card ▸ Subgroup.card_dvd_of_le le_sup_right
    have hdvd15 : 15 ∣ Nat.card N := by
      simpa using (by norm_num : Nat.Coprime 3 5).mul_dvd_of_dvd_of_dvd hdvd3 hdvd5
    obtain ⟨k, hk⟩ := hdvd15
    have hpos : 0 < Nat.card N := Nat.card_pos
    omega
  constructor
  · exact ⟨N, inferInstance, hNcard⟩
  · intro H hH
    rcases hH with hH | hH | hH
    · exact apm_b96a02_normal_of_card_three_of_unique_sylow G hG h3 H hH
    · exact apm_b96a02_normal_of_card_five_of_unique_sylow G hG h5 H hH
    · exact apm_b96a02_normal_of_card_fifteen G hG H hH

theorem apm_b96a02 :
    (∀ (G : Type*) [Group G] [Fintype G], Fintype.card G = 30 →
      (∃ N : Subgroup G, N.Normal ∧ Nat.card N = 15) ∧
      (∀ H : Subgroup G,
        Nat.card H = 3 ∨ Nat.card H = 5 ∨ Nat.card H = 15 → H.Normal)) ∧
    (∀ (F L : Type*) [Field F] [Field L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L] (α : L),
      (minpoly F α).IsSplittingField F L ↔
        (IntermediateField.adjoin F {α}).fixingSubgroup.normalCore = ⊥) ∧
    (∀ (F L : Type*) [Field F] [Field L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L] (α : L),
      Nat.card (L ≃ₐ[F] L) = 30 →
      (minpoly F α).IsSplittingField F L →
        (minpoly F α).natDegree = 15 ∨ (minpoly F α).natDegree = 30) ∧
    (∀ (F L : Type*) [Field F] [Field L] [Algebra F L]
      [FiniteDimensional F L] [IsGalois F L],
      Nat.card (L ≃ₐ[F] L) = 18 →
      (∃ f : F[X], f.natDegree = 6 ∧ f.IsSplittingField F L) →
        ∃ g : F[X], g.natDegree = 9 ∧ g.IsSplittingField F L) := by
  constructor
  · -- Boundary (closer hop 1): searched the Sylow counting APIs (`Sylow.card_eq_multiplicity`,
    -- `Sylow.card_dvd_index`, `card_sylow_modEq_one`,
    -- `Sylow.normal_of_subsingleton`, and `Subgroup.normal_of_index_eq_two`).
    -- Mathlib has no packaged order-30 theorem; formalizing the incompatible
    -- simultaneous Sylow counts and then the characteristic order-3/order-5
    -- subgroups inside the normal order-15 subgroup exceeded pass-1.
    -- This hop additionally checked `GroupTheory/SpecificGroups/ZGroup.lean`.
    -- Since 30 is squarefree, `IsZGroup.of_squarefree` supplies cyclic Sylow
    -- subgroups, and `IsZGroup.isZGroup_iff_exists_mulEquiv` supplies an abstract
    -- semidirect-product classification.  However, extracting from that
    -- classification a normal subgroup of the *specific* cardinality 15 still
    -- requires arithmetic classification of the two coprime factors (or the
    -- original Sylow count).  No theorem specialized to cardinality 30 was
    -- found in Mathlib, `LEMMA-INDEX.md`, or closed sibling artifacts.
    -- Closer hop 2 proves `apm_b96a02_normal_of_card_fifteen`: once an
    -- order-15 subgroup is constructed, `Subgroup.card_mul_index` computes its
    -- index as two and `Subgroup.normal_of_index_eq_two` proves it normal.
    -- Thus the remaining group-theoretic boundary is construction of such a
    -- subgroup and normality of the order-3 and order-5 subgroups.
    -- Closer hop 3 proves
    -- `apm_b96a02_normalCore_eq_bot_or_eq_self_of_prime_card`: for any
    -- prime-order subgroup its normal core is either bottom or the subgroup
    -- itself.  This uses the prime-cardinality subgroup dichotomy on
    -- `H.normalCore.subgroupOf H`.  It reduces the order-3/order-5 normality
    -- and the later core-free analysis to excluding the bottom-core branch,
    -- but it does not construct the required order-15 subgroup.  Further
    -- searches of Hall-subgroup and finite-solvable-group APIs found no
    -- existence theorem applicable to arbitrary groups of order 30.
    intro G _ _ hG
    exact apm_b96a02_order_thirty_group G hG
  constructor
  · -- Boundary (closer hop 1): searched `IntermediateField.fixingSubgroup`,
    -- `Subgroup.normalCore_eq_iInf_conjAct`, `Subgroup.normal_le_normalCore`,
    -- `IntermediateField.normalClosure_def''`, and the Galois correspondence.
    -- These expose the dual intersection-of-conjugates/supremum-of-conjugate-
    -- fields route, but the exact theorem identifying the fixed field of the
    -- core with the normal closure, followed by the simple-extension root-set
    -- characterization of a minimal-polynomial splitting field, is not
    -- packaged in Mathlib.
    -- This hop narrowed the group/field bridge: `normalClosure_def''` expresses
    -- the normal closure as the supremum of all conjugate fields, while
    -- `IntermediateField.fixingSubgroup_sup` turns binary suprema into infima;
    -- `IntermediateField.le_iff_le` and `Subgroup.normal_le_normalCore` can also
    -- prove directly that the fixing subgroup of the normal closure is the
    -- normal core.  The remaining unproved bridge is specifically
    -- `normalClosure F (adjoin F {alpha}) L = adjoin F ((minpoly F alpha).rootSet L)`.
    -- `Normal/Closure.lean` has only the iSup-over-all-elements formula and even
    -- records a TODO for a general `isNormalClosure_iff`; no simple-extension
    -- specialization was found.  Establishing it locally requires extending
    -- embeddings and identifying all conjugates of `alpha` with the root set.
    intro F L _ _ _ _ _ α
    have hsplits : ((minpoly F α).map (algebraMap F L)).Splits := IsGalois.splits F α
    rw [isSplittingField_iff_intermediateField]
    simp only [hsplits, true_and]
    rw [← apm_b96a02_normalClosure_adjoin_simple F L α]
    rw [← apm_b96a02_fixingSubgroup_normalClosure F L
      (IntermediateField.adjoin F {α})]
    constructor
    · intro h
      rw [h, IntermediateField.fixingSubgroup_top]
    · intro h
      apply (IsGalois.intermediateFieldEquivSubgroup :
        IntermediateField F L ≃o (Subgroup (L ≃ₐ[F] L))ᵒᵈ).injective
      exact h.trans IntermediateField.fixingSubgroup_top.symm
  constructor
  · -- Boundary (closer hop 1): this depends on both preceding missing developments plus
    -- index/degree bookkeeping for the fixing subgroup; APIs searched include
    -- `IntermediateField.finrank_eq_card_fixingSubgroup`,
    -- `Subgroup.normalCore_le`, Cauchy's theorem, and subgroup-cardinality
    -- divisibility.  Without the order-30 normal-subgroup theorem and the
    -- core/splitting-field bridge, the exclusion of subgroup orders 3 and 5
    -- cannot yet be transported to the asserted minimal-polynomial degrees.
    -- The new `IsZGroup` route does not bypass those dependencies: its
    -- semidirect factors are existential and do not directly classify every
    -- core-free subgroup.  No closed sibling packages the required order-30
    -- core-free-subgroup index classification.  The closer-hop-3 prime-order
    -- normal-core dichotomy now isolates the needed contradiction for subgroup
    -- orders 3 and 5: one must prove those subgroups normal in the order-30
    -- group, after which their core cannot be bottom.  That final normality
    -- input is exactly the still-open first conjunct.
    intro F L _ _ _ _ _ α hcard hsplit
    apply apm_b96a02_degree_of_small_subgroups_normal F L α hcard
    intro H hH
    exact (apm_b96a02_order_thirty_group (L ≃ₐ[F] L)
      (by simpa [Nat.card_eq_fintype_card] using hcard)).2 H
      (hH.elim Or.inl (fun h => Or.inr (Or.inl h)))
    exact hsplit
  · intro F L _ _ _ _ _ hcard hex
    obtain ⟨f, hfdeg, hf⟩ := hex
    have hf0 : f ≠ 0 := by
      intro h
      subst f
      simp at hfdeg
    letI : f.IsSplittingField F L := hf
    letI : (X ^ 3 : L[X]).IsSplittingField L L := by
      constructor
      · simp
      · simp [Polynomial.rootSet]
    letI : ((X ^ 3 : F[X]).map (algebraMap F L)).IsSplittingField L L := by
      simpa using (inferInstance : (X ^ 3 : L[X]).IsSplittingField L L)
    refine ⟨f * X ^ 3, ?_, ?_⟩
    · rw [natDegree_mul hf0 (pow_ne_zero 3 X_ne_zero), natDegree_pow]
      simp [hfdeg]
    · exact Polynomial.IsSplittingField.mul (F := F) (K := L) L f (X ^ 3) hf0
        (pow_ne_zero 3 X_ne_zero)
