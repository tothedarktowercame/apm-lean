import Mathlib

open scoped Pointwise

lemma apm_b99A02_factorization_203_29 : (Nat.factorization 203) 29 = 1 := by
  rw [show 203 = 7 * 29 by norm_num,
    Nat.factorization_mul (by norm_num : 7 ≠ 0) (by norm_num : 29 ≠ 0)]
  norm_num [Nat.factorization_def]

lemma apm_b99A02_factorization_725_29 : (Nat.factorization 725) 29 = 1 := by
  rw [show 725 = 5^2 * 29 by norm_num,
    Nat.factorization_mul (by norm_num : 5^2 ≠ 0) (by norm_num : 29 ≠ 0)]
  norm_num [Nat.factorization_def]

lemma apm_b99A02_factorization_175_7 : (Nat.factorization 175) 7 = 1 := by
  rw [show 175 = 5^2 * 7 by norm_num,
    Nat.factorization_mul (by norm_num : 5^2 ≠ 0) (by norm_num : 7 ≠ 0)]
  norm_num [Nat.factorization_def]

lemma apm_b99A02_factorization_5075_5 : (Nat.factorization 5075) 5 = 2 := by
  rw [show 5075 = 5^2 * 7 * 29 by norm_num,
    Nat.factorization_mul (by norm_num : 5^2 * 7 ≠ 0) (by norm_num : 29 ≠ 0),
    Nat.factorization_mul (by norm_num : 5^2 ≠ 0) (by norm_num : 7 ≠ 0),
    Nat.factorization_pow]
  norm_num [Nat.factorization_def]

lemma apm_b99A02_factorization_5075_7 : (Nat.factorization 5075) 7 = 1 := by
  rw [show 5075 = 5^2 * 7 * 29 by norm_num,
    Nat.factorization_mul (by norm_num : 5^2 * 7 ≠ 0) (by norm_num : 29 ≠ 0),
    Nat.factorization_mul (by norm_num : 5^2 ≠ 0) (by norm_num : 7 ≠ 0)]
  norm_num [Nat.factorization_def]

lemma apm_b99A02_factorization_5075_29 : (Nat.factorization 5075) 29 = 1 := by
  rw [show 5075 = 5^2 * 7 * 29 by norm_num,
    Nat.factorization_mul (by norm_num : 5^2 * 7 ≠ 0) (by norm_num : 29 ≠ 0),
    Nat.factorization_mul (by norm_num : 5^2 ≠ 0) (by norm_num : 7 ≠ 0)]
  norm_num [Nat.factorization_def]

attribute [simp] apm_b99A02_factorization_203_29 apm_b99A02_factorization_725_29
  apm_b99A02_factorization_175_7 apm_b99A02_factorization_5075_5
  apm_b99A02_factorization_5075_7 apm_b99A02_factorization_5075_29

/-!
# APM b99A02

## Statement repairs

None.

## Encoding questions

None.
-/

/-- The structural pullback step in the Sylow cascade: a normal subgroup of a
quotient pulls back to a normal subgroup containing the quotient kernel. -/
lemma apm_b99A02_normal_comap_mk_and_le
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (S : Subgroup (G ⧸ N)) (hS : S.Normal) :
    (S.comap (QuotientGroup.mk' N)).Normal ∧
      N ≤ S.comap (QuotientGroup.mk' N) := by
  exact ⟨hS.comap (QuotientGroup.mk' N), QuotientGroup.le_comap_mk' N S⟩

lemma apm_b99A02_card_comap_mk
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (S : Subgroup (G ⧸ N)) :
    Nat.card (S.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card S := by
  simpa only [Set.mem_preimage, SetLike.mem_coe] using
    (QuotientGroup.card_preimage_mk N (S : Set (G ⧸ N)))

lemma apm_b99A02_sylow29_unique_of_card_203
    (X : Type*) [Group X] [Fintype X] (hX : Nat.card X = 203) :
    Nat.card (Sylow 29 X) = 1 := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  let S : Sylow 29 X := default
  have hScard : Nat.card S = 29 := by
    rw [Sylow.card_eq_multiplicity, hX]
    norm_num
  have hSindex : S.index = 7 := by
    have h := S.toSubgroup.index_mul_card
    rw [hScard, hX] at h
    omega
  have hdvd : Nat.card (Sylow 29 X) ∣ 7 := by
    simpa [hSindex] using Sylow.card_dvd_index S
  have hnmem : Nat.card (Sylow 29 X) ∈ Nat.divisors 7 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 7 = {1, 7} := by decide
  rw [hdivs] at hnmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
  rcases hnmem with h1 | h7
  · exact h1
  · have hmod : Nat.card (Sylow 29 X) ≡ 1 [MOD 29] :=
      card_sylow_modEq_one 29 X
    rw [h7] at hmod
    norm_num [Nat.ModEq] at hmod

lemma apm_b99A02_sylow29_normal_of_card_203
    (X : Type*) [Group X] [Fintype X] (hX : Nat.card X = 203)
    (S : Sylow 29 X) : S.toSubgroup.Normal := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  haveI : Subsingleton (Sylow 29 X) :=
    (Nat.card_eq_one_iff_unique.mp
      (apm_b99A02_sylow29_unique_of_card_203 X hX)).1
  exact Sylow.normal_of_subsingleton S

lemma apm_b99A02_sylow29_unique_of_card_725
    (X : Type*) [Group X] [Fintype X] (hX : Nat.card X = 725) :
    Nat.card (Sylow 29 X) = 1 := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  let S : Sylow 29 X := default
  have hScard : Nat.card S = 29 := by
    rw [Sylow.card_eq_multiplicity, hX]
    norm_num
  have hSindex : S.index = 25 := by
    have h := S.toSubgroup.index_mul_card
    rw [hScard, hX] at h
    omega
  have hdvd : Nat.card (Sylow 29 X) ∣ 25 := by
    simpa [hSindex] using Sylow.card_dvd_index S
  have hnmem : Nat.card (Sylow 29 X) ∈ Nat.divisors 25 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 25 = {1, 5, 25} := by decide
  rw [hdivs] at hnmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
  rcases hnmem with h1 | h5 | h25
  · exact h1
  · have hmod : Nat.card (Sylow 29 X) ≡ 1 [MOD 29] := card_sylow_modEq_one 29 X
    rw [h5] at hmod
    norm_num [Nat.ModEq] at hmod
  · have hmod : Nat.card (Sylow 29 X) ≡ 1 [MOD 29] := card_sylow_modEq_one 29 X
    rw [h25] at hmod
    norm_num [Nat.ModEq] at hmod

lemma apm_b99A02_sylow7_unique_of_card_175
    (X : Type*) [Group X] [Fintype X] (hX : Nat.card X = 175) :
    Nat.card (Sylow 7 X) = 1 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let S : Sylow 7 X := default
  have hScard : Nat.card S = 7 := by
    rw [Sylow.card_eq_multiplicity, hX]
    norm_num
  have hSindex : S.index = 25 := by
    have h := S.toSubgroup.index_mul_card
    rw [hScard, hX] at h
    omega
  have hdvd : Nat.card (Sylow 7 X) ∣ 25 := by
    simpa [hSindex] using Sylow.card_dvd_index S
  have hnmem : Nat.card (Sylow 7 X) ∈ Nat.divisors 25 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 25 = {1, 5, 25} := by decide
  rw [hdivs] at hnmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
  rcases hnmem with h1 | h5 | h25
  · exact h1
  · have hmod : Nat.card (Sylow 7 X) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 X
    rw [h5] at hmod
    norm_num [Nat.ModEq] at hmod
  · have hmod : Nat.card (Sylow 7 X) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 X
    rw [h25] at hmod
    norm_num [Nat.ModEq] at hmod

lemma apm_b99A02_sylow29_normal_from_normal_725
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 5075)
    (H : Subgroup G) [H.Normal] (hH : Nat.card H = 725)
    (Q : Sylow 29 G) : Q.toSubgroup.Normal := by
  letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  letI : Fintype H := Fintype.ofFinite H
  let T : Sylow 29 H := default
  have hTcard : Nat.card T = 29 := by
    rw [Sylow.card_eq_multiplicity, hH]
    norm_num
  haveI : Subsingleton (Sylow 29 H) :=
    (Nat.card_eq_one_iff_unique.mp
      (apm_b99A02_sylow29_unique_of_card_725 H hH)).1
  haveI : T.toSubgroup.Characteristic := Sylow.characteristic_of_subsingleton T
  haveI hTnormal : (T.toSubgroup.map H.subtype).Normal := inferInstance
  have hmapcard : Nat.card (T.toSubgroup.map H.subtype) = 29 := by
    rw [Subgroup.card_subtype, hTcard]
  let U : Sylow 29 G := Sylow.ofCard (T.toSubgroup.map H.subtype) (by
    rw [hmapcard, hG]
    norm_num)
  have hUnormal : U.toSubgroup.Normal := by
    change (T.toSubgroup.map H.subtype).Normal
    exact hTnormal
  letI : Unique (Sylow 29 G) := Sylow.unique_of_normal U hUnormal
  exact Sylow.normal_of_subsingleton Q

lemma apm_b99A02_card_sup_sylow5_sylow7
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 5075)
    (P : Sylow 5 G) (R : Sylow 7 G) [P.toSubgroup.Normal] :
    Nat.card ↥((P : Subgroup G) ⊔ (R : Subgroup G)) = 175 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hPcard : Nat.card P = 25 := by
    rw [Sylow.card_eq_multiplicity, hG]
    norm_num
  have hRcard : Nat.card R = 7 := by
    rw [Sylow.card_eq_multiplicity, hG]
    norm_num
  have hdisj : Disjoint P.toSubgroup R.toSubgroup :=
    IsPGroup.disjoint_of_ne 5 7 (by norm_num) _ _ P.isPGroup' R.isPGroup'
  let K : Subgroup G := (P : Subgroup G) ⊔ (R : Subgroup G)
  let f : Prod P R → K := fun x => ⟨(x.1 : G) * (x.2 : G), by
    change (x.1 : G) * (x.2 : G) ∈ (K : Set G)
    rw [show (K : Set G) = (P.toSubgroup : Set G) * (R.toSubgroup : Set G) by
      exact Subgroup.normal_mul _ _]
    exact ⟨x.1, x.1.property, x.2, x.2.property, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact Subtype.ext_iff.mp hxy
  have hf_surj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    change g ∈ (K : Set G) at hg
    rw [show (K : Set G) = (P.toSubgroup : Set G) * (R.toSubgroup : Set G) by
      exact Subgroup.normal_mul _ _] at hg
    rcases hg with ⟨p, hp, r, hr, rfl⟩
    exact ⟨(⟨p, hp⟩, ⟨r, hr⟩), rfl⟩
  have hcard : Nat.card (Prod P R) = Nat.card K :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
  rw [Nat.card_prod, hPcard, hRcard] at hcard
  exact hcard.symm

lemma apm_b99A02_prime_dvd_5075 (p : ℕ) (hp : p.Prime) (h : p ∣ 5075) :
    p = 5 ∨ p = 7 ∨ p = 29 := by
  have h' : p ∣ 5 ^ 2 * 7 * 29 := by norm_num at h ⊢; exact h
  rcases hp.dvd_mul.mp h' with h | h
  · rcases hp.dvd_mul.mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow h))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))

lemma apm_b99A02_sylow7_normal_from_normal_175
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 5075)
    (K : Subgroup G) [K.Normal] (hK : Nat.card K = 175)
    (R : Sylow 7 G) : R.toSubgroup.Normal := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : Fintype K := Fintype.ofFinite K
  let T : Sylow 7 K := default
  have hTcard : Nat.card T = 7 := by
    rw [Sylow.card_eq_multiplicity, hK]
    norm_num
  haveI : Subsingleton (Sylow 7 K) :=
    (Nat.card_eq_one_iff_unique.mp
      (apm_b99A02_sylow7_unique_of_card_175 K hK)).1
  haveI : T.toSubgroup.Characteristic := Sylow.characteristic_of_subsingleton T
  haveI hTnormal : (T.toSubgroup.map K.subtype).Normal := inferInstance
  have hmapcard : Nat.card (T.toSubgroup.map K.subtype) = 7 := by
    rw [Subgroup.card_subtype, hTcard]
  let U : Sylow 7 G := Sylow.ofCard (T.toSubgroup.map K.subtype) (by
    rw [hmapcard, hG]
    norm_num)
  have hUnormal : U.toSubgroup.Normal := by
    change (T.toSubgroup.map K.subtype).Normal
    exact hTnormal
  letI : Unique (Sylow 7 G) := Sylow.unique_of_normal U hUnormal
  exact Sylow.normal_of_subsingleton R

lemma apm_b99A02_sylow_commutative_of_card_5075
    {G : Type*} [Group G] [Fintype G] (hG : Nat.card G = 5075)
    {p : ℕ} [Fact p.Prime] (T : Sylow p G) : ∀ a b : T, a * b = b * a := by
  by_cases hdvd : p ∣ 5075
  · rcases apm_b99A02_prime_dvd_5075 p Fact.out hdvd with rfl | rfl | rfl
    · apply IsPGroup.commutative_of_card_eq_prime_sq (p := 5)
      change Nat.card T.toSubgroup = 5 ^ 2
      rw [Sylow.card_eq_multiplicity, hG]
      norm_num
    · have hc : Nat.card T = 7 := by
        change Nat.card T.toSubgroup = 7
        rw [Sylow.card_eq_multiplicity, hG]
        norm_num
      letI := (isCyclic_of_prime_card (p := 7) hc).commutative
      exact fun a b => Std.Commutative.comm a b
    · have hc : Nat.card T = 29 := by
        change Nat.card T.toSubgroup = 29
        rw [Sylow.card_eq_multiplicity, hG]
        norm_num
      letI := (isCyclic_of_prime_card (p := 29) hc).commutative
      exact fun a b => Std.Commutative.comm a b
  · have hTcard : Nat.card T = 1 := by
      rw [Sylow.card_eq_multiplicity, hG,
        Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
    haveI : Subsingleton T :=
      (Nat.card_eq_one_iff_unique.mp hTcard).1
    intro a b
    exact Subsingleton.elim _ _

theorem apm_b99a02
    (G : Type*) [Group G] [Fintype G]
    (hG : Fintype.card G = 5075)
    (P : Sylow 5 G) (Q : Sylow 29 G) (R : Sylow 7 G) :
    P.toSubgroup.Normal ∧
      (∃ H : Subgroup G, H.Normal ∧ Nat.card H = 5 ^ 2 * 29) ∧
      Q.toSubgroup.Normal ∧
      ∃ K : Subgroup G,
        Nat.card K = 5 ^ 2 * 7 ∧
          (K.Normal ↔ ∀ a b : G, a * b = b * a) := by
  have hGcard : Nat.card G = 5075 := by simpa using hG
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hPcard : Nat.card P = 25 := by
    rw [Sylow.card_eq_multiplicity, hGcard]
    norm_num
  have hPindex : P.index = 203 := by
    have h := P.toSubgroup.index_mul_card
    rw [hPcard, hGcard] at h
    omega
  have hSylow5card : Nat.card (Sylow 5 G) = 1 := by
    have hdvd : Nat.card (Sylow 5 G) ∣ 203 := by
      simpa [hPindex] using Sylow.card_dvd_index P
    have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] :=
      card_sylow_modEq_one 5 G
    have hle : Nat.card (Sylow 5 G) ≤ 203 :=
      Nat.le_of_dvd (by norm_num) hdvd
    have hnmem : Nat.card (Sylow 5 G) ∈ Nat.divisors 203 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdivs : Nat.divisors 203 = {1, 7, 29, 203} := by decide
    rw [hdivs] at hnmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
    rcases hnmem with h1 | h7 | h29 | h203
    · exact h1
    · rw [h7] at hmod
      norm_num [Nat.ModEq] at hmod
    · rw [h29] at hmod
      norm_num [Nat.ModEq] at hmod
    · rw [h203] at hmod
      norm_num [Nat.ModEq] at hmod
  haveI : Subsingleton (Sylow 5 G) :=
    (Nat.card_eq_one_iff_unique.mp hSylow5card).1
  have hPnormal : P.toSubgroup.Normal := Sylow.normal_of_subsingleton P
  letI : P.toSubgroup.Normal := hPnormal
  have hquotcard : Nat.card (G ⧸ P.toSubgroup) = 203 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup P.toSubgroup
    rw [hGcard, hPcard] at h
    omega
  letI : Fintype (G ⧸ P.toSubgroup) := Fintype.ofFinite _
  let S : Sylow 29 (G ⧸ P.toSubgroup) := default
  have hSnormal : S.toSubgroup.Normal :=
    apm_b99A02_sylow29_normal_of_card_203 (G ⧸ P.toSubgroup) hquotcard S
  have hScard : Nat.card S = 29 := by
    letI : Fact (Nat.Prime 29) := ⟨by norm_num⟩
    rw [Sylow.card_eq_multiplicity, hquotcard]
    norm_num
  let H : Subgroup G := S.toSubgroup.comap (QuotientGroup.mk' P.toSubgroup)
  have hHnormal : H.Normal :=
    (apm_b99A02_normal_comap_mk_and_le P.toSubgroup S.toSubgroup hSnormal).1
  have hHcard : Nat.card H = 5 ^ 2 * 29 := by
    dsimp [H]
    rw [apm_b99A02_card_comap_mk, hPcard, hScard]
  constructor
  · exact hPnormal
  constructor
  · exact ⟨H, hHnormal, hHcard⟩
  letI : H.Normal := hHnormal
  have hQnormal : Q.toSubgroup.Normal :=
    apm_b99A02_sylow29_normal_from_normal_725 hGcard H (by norm_num at hHcard ⊢; exact hHcard) Q
  refine ⟨hQnormal, ?_⟩
  let K : Subgroup G := (P : Subgroup G) ⊔ (R : Subgroup G)
  have hKcard : Nat.card K = 5 ^ 2 * 7 := by
    simpa [K] using apm_b99A02_card_sup_sylow5_sylow7 hGcard P R
  refine ⟨K, hKcard, ?_⟩
  constructor
  · intro hKnormal
    letI : K.Normal := hKnormal
    have hRnormal : R.toSubgroup.Normal :=
      apm_b99A02_sylow7_normal_from_normal_175 hGcard K (by norm_num at hKcard ⊢; exact hKcard) R
    have hn : ∀ {p : ℕ} [Fact p.Prime] (T : Sylow p G), T.toSubgroup.Normal := by
      intro p hp T
      by_cases hdvd : p ∣ 5075
      · rcases apm_b99A02_prime_dvd_5075 p hp.out hdvd with rfl | rfl | rfl
        · exact Subsingleton.elim T P ▸ hPnormal
        · letI : Unique (Sylow 7 G) := Sylow.unique_of_normal R hRnormal
          exact Sylow.normal_of_subsingleton T
        · letI : Unique (Sylow 29 G) := Sylow.unique_of_normal Q hQnormal
          exact Sylow.normal_of_subsingleton T
      · have hTcard : Nat.card T = 1 := by
          rw [Sylow.card_eq_multiplicity, hGcard,
            Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
        have hTbot : T.toSubgroup = ⊥ := T.toSubgroup.eq_bot_of_card_eq hTcard
        rw [hTbot]
        infer_instance
    let e := Sylow.directProductOfNormal hn
    intro a b
    rw [← e.apply_symm_apply a, ← e.apply_symm_apply b, ← e.map_mul, ← e.map_mul]
    congr 1
    funext p T
    letI : Fact (Nat.Prime (p : ℕ)) := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    exact apm_b99A02_sylow_commutative_of_card_5075 hGcard T _ _
  · intro hcomm
    constructor
    intro n hn g
    simpa [hcomm] using hn

#print axioms apm_b99a02
