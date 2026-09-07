import Mathlib

open scoped Pointwise

/-!
# APM b98A01

## Statement repairs

In part (b)(iv), “a subgroup of order `3`” is repaired to “a subgroup of
order `35`”. An order-`3` subgroup exists unconditionally by Cauchy's theorem
because `3 ∣ 210`; it cannot be the contingent index-six subgroup to which the
hint says to apply part (a). The order-`35` statement is the substantive
equivalence used by that core argument.

## Encoding questions

None. Part (a) uses an actual homomorphism to `Equiv.Perm (Fin n)` and states
the universal property of its kernel. Part (b) uses actual subgroup
normalizers, subgroup cardinalities, and normality.
-/

/-- The numerical Sylow alternatives for the number of order-five Sylow
subgroups in a group of order `210`. -/
lemma apm_b98a01_sylow5_count_arithmetic
    (s : ℕ) (hdvd : s ∣ 42) (hmod : s % 5 = 1) (hne : s ≠ 1) :
    s = 6 ∨ s = 21 := by
  have hpos : 0 < s := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : s ≤ 42 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases s
  all_goals norm_num at *

/-- Converting the two Sylow-count alternatives into normalizer cardinalities. -/
lemma apm_b98a01_normalizer_card_arithmetic
    (s c : ℕ) (hprod : s * c = 210) (hs : s = 6 ∨ s = 21) :
    c = 10 ∨ c = 35 := by
  rcases hs with rfl | rfl <;> omega

/-- In a group of order `210`, every subgroup of order five is a Sylow
five-subgroup. -/
noncomputable def apm_b98a01_orderFiveSylow
    (G : Type*) [Group G] [Fintype G] (B : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5) : Sylow 5 G := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  apply Sylow.ofCard B
  have hG' : Nat.card G = 210 := by
    simpa [Nat.card_eq_fintype_card] using hG
  rw [hB, hG']
  have hf : Nat.factorization 210 5 = 1 := by
    rw [Nat.factorization_def 210 (by norm_num : Nat.Prime 5),
      show 210 = 5 * 42 by norm_num,
      padicValNat_base_mul (p := 5) (n := 42) (by norm_num) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
  rw [hf]
  norm_num

@[simp] lemma apm_b98a01_orderFiveSylow_coe
    (G : Type*) [Group G] [Fintype G] (B : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5) :
    (apm_b98a01_orderFiveSylow G B hG hB : Subgroup G) = B := rfl

/-- The index of any order-five subgroup in an order-`210` group is `42`. -/
lemma apm_b98a01_orderFive_index
    (G : Type*) [Group G] [Fintype G] (B : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5) :
    B.index = 42 := by
  have hprod := B.card_mul_index
  rw [hB, show Nat.card G = 210 by
    simpa [Nat.card_eq_fintype_card] using hG] at hprod
  omega

/-- The Sylow theorems and the arithmetic helpers give the two possible
normalizer cardinalities for a nonnormal order-five subgroup. -/
lemma apm_b98a01_orderFive_normalizer_card
    (G : Type*) [Group G] [Fintype G] (B : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5)
    (hnormal : ¬B.Normal) :
    Nat.card (Subgroup.normalizer (B : Set G)) = 10 ∨
      Nat.card (Subgroup.normalizer (B : Set G)) = 35 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 G := apm_b98a01_orderFiveSylow G B hG hB
  let s := Nat.card (Sylow 5 G)
  have hindex : (P : Subgroup G).index = 42 := by
    simpa [P] using apm_b98a01_orderFive_index G B hG hB
  have hdvd : s ∣ 42 := by
    simpa [s, hindex] using P.card_dvd_index
  have hmod : s % 5 = 1 := by
    have hm := card_sylow_modEq_one 5 G
    change s % 5 = 1 % 5 at hm
    simpa using hm
  have hsne : s ≠ 1 := by
    intro hs
    letI : Subsingleton (Sylow 5 G) := (Nat.card_eq_one_iff_unique.mp hs).1
    have hpnormal : (P : Subgroup G).Normal := P.normal_of_subsingleton
    apply hnormal
    simpa [P] using hpnormal
  have hs := apm_b98a01_sylow5_count_arithmetic s hdvd hmod hsne
  let c := Nat.card (Subgroup.normalizer (B : Set G))
  have hnormalizerIndex :
      (Subgroup.normalizer (B : Set G)).index = s := by
    change (Subgroup.normalizer ((P : Subgroup G) : Set G)).index = s
    simpa [s] using (Sylow.card_eq_index_normalizer P).symm
  have hprod0 := (Subgroup.normalizer (B : Set G)).card_mul_index
  have hcardG : Nat.card G = 210 := by
    simpa [Nat.card_eq_fintype_card] using hG
  have hprod : s * c = 210 := by
    rw [hnormalizerIndex, hcardG] at hprod0
    simpa [s, c, Nat.mul_comm] using hprod0
  exact apm_b98a01_normalizer_card_arithmetic s c hprod hs

/-- The coset action, transported to `Fin n`, realizes the normal core as a
permutation kernel and has the required universal property. -/
lemma apm_b98a01_coset_core_action
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G) (n : ℕ)
    (hn : H.index = n) :
    ∃ ψ : G →* Equiv.Perm (Fin n),
      MonoidHom.ker ψ ≤ H ∧
      ∀ N : Subgroup G, N.Normal → N ≤ H → N ≤ MonoidHom.ker ψ := by
  letI : Fintype (G ⧸ H) := Fintype.ofFinite (G ⧸ H)
  have hc : Fintype.card (G ⧸ H) = n := by
    rw [← Nat.card_eq_fintype_card, ← H.index_eq_card, hn]
  let e : (G ⧸ H) ≃ Fin n := Fintype.equivFinOfCardEq hc
  let ψ : G →* Equiv.Perm (Fin n) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))
  have hker : MonoidHom.ker ψ = H.normalCore := by
    rw [Subgroup.normalCore_eq_ker]
    ext g
    simp [ψ]
  refine ⟨ψ, hker.le.trans H.normalCore_le, ?_⟩
  intro N hN hNH
  letI : N.Normal := hN
  rw [hker]
  exact Subgroup.normal_le_normalCore.mpr hNH

/-- A normal subgroup of order seven lifts an order-five subgroup of the
quotient to a subgroup of order thirty-five. -/
lemma apm_b98a01_order35_of_normal_order7
    (G : Type*) [Group G] [Fintype G] (N : Subgroup G)
    (hG : Fintype.card G = 210) (hNnormal : N.Normal) (hN : Nat.card N = 7) :
    ∃ M : Subgroup G, Nat.card M = 35 := by
  letI : N.Normal := hNnormal
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  have hq : Fintype.card (G ⧸ N) = 30 := by
    have hcard := N.card_eq_card_quotient_mul_card_subgroup
    rw [show Nat.card G = 210 by
      simpa [Nat.card_eq_fintype_card] using hG,
      show Nat.card (G ⧸ N) = Fintype.card (G ⧸ N) by
        simp [Nat.card_eq_fintype_card], hN] at hcard
    omega
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ : ∃ x : G ⧸ N, orderOf x = 5 := by
    apply exists_prime_orderOf_dvd_card 5
    rw [hq]
    norm_num
  let Q : Subgroup (G ⧸ N) := Subgroup.zpowers x
  let M : Subgroup G := Q.comap (QuotientGroup.mk' N)
  refine ⟨M, ?_⟩
  have hQcard : Nat.card Q = 5 := by
    change Nat.card (Subgroup.zpowers x) = 5
    exact (Nat.card_zpowers x).trans hx
  have hQindex : Q.index = 6 := by
    have hp := Q.card_mul_index
    rw [hQcard, show Nat.card (G ⧸ N) = 30 by
      simpa [Nat.card_eq_fintype_card] using hq] at hp
    omega
  have hMindex : M.index = 6 := by
    rw [show M.index = Q.index by
      exact Q.index_comap_of_surjective (QuotientGroup.mk'_surjective N), hQindex]
  have hp := M.card_mul_index
  rw [hMindex, show Nat.card G = 210 by
    simpa [Nat.card_eq_fintype_card] using hG] at hp
  omega

/-- The elementary divisibility constraints on the kernel of an index-six
coset action attached to an order-thirty-five subgroup. -/
lemma apm_b98a01_core_card_arithmetic
    (k i : ℕ) (hk : k ∣ 35) (hki : k * i = 210) (hi : i ∣ 720) :
    k = 7 ∨ k = 35 := by
  rcases hi with ⟨j, hj⟩
  have hkpos : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    simp [hkzero] at hki
  have hkle : k ≤ 35 := Nat.le_of_dvd (by norm_num) hk
  interval_cases k
  all_goals norm_num at hk
  all_goals try norm_num
  case «1» =>
    have hi210 : i = 210 := by omega
    subst i
    omega
  case «5» =>
    have hi42 : i = 42 := by omega
    subst i
    omega

set_option maxHeartbeats 0 in
/-- A normal subgroup of order thirty-five contains a characteristic Sylow
seven-subgroup, which is therefore normal in the ambient group. -/
lemma apm_b98a01_normal_order7_of_normal_order35
    (G : Type*) [Group G] [Fintype G] (H : Subgroup G)
    (hHnormal : H.Normal) (hH : Nat.card H = 35) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7 := by
  letI : H.Normal := hHnormal
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let P : Sylow 7 H := default
  have hPcard : Nat.card P = 7 := by
    rw [P.card_eq_multiplicity, hH]
    rw [Nat.factorization_def 35 (by norm_num : Nat.Prime 7),
      show 35 = 7 * 5 by norm_num,
      padicValNat_base_mul (p := 7) (n := 5) (by norm_num) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hPindex : (P : Subgroup H).index = 5 := by
    have hp := (P : Subgroup H).card_mul_index
    rw [hPcard, hH] at hp
    omega
  let s := Nat.card (Sylow 7 H)
  have hsdvd : s ∣ 5 := by
    simpa [s, hPindex] using P.card_dvd_index
  have hsmod : s % 7 = 1 := by
    have hm := card_sylow_modEq_one 7 H
    change s % 7 = 1 % 7 at hm
    simpa using hm
  have hs : s = 1 := by
    have hspos : 0 < s := Nat.card_pos
    have hsle : s ≤ 5 := Nat.le_of_dvd (by norm_num) hsdvd
    rw [Nat.mod_eq_of_lt (by omega)] at hsmod
    exact hsmod
  letI : Subsingleton (Sylow 7 H) := (Nat.card_eq_one_iff_unique.mp hs).1
  letI : P.Characteristic := Sylow.characteristic_of_subsingleton P
  let N : Subgroup G := (P : Subgroup H).map H.subtype
  refine ⟨N, inferInstance, ?_⟩
  change Nat.card ((P : Subgroup H).map H.subtype) = 7
  exact (Nat.card_congr
    ((P : Subgroup H).equivMapOfInjective H.subtype Subtype.coe_injective).toEquiv).symm.trans hPcard

/-- Any order-thirty-five subgroup yields a normal order-seven subgroup by
examining the kernel of its action on the six cosets. -/
lemma apm_b98a01_normal_order7_of_order35
    (G : Type*) [Group G] [Fintype G] (M : Subgroup G)
    (hG : Fintype.card G = 210) (hM : Nat.card M = 35) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7 := by
  have hMindex : M.index = 6 := by
    have hp := M.card_mul_index
    rw [hM, show Nat.card G = 210 by
      simpa [Nat.card_eq_fintype_card] using hG] at hp
    omega
  obtain ⟨ψ, hkerle, _⟩ := apm_b98a01_coset_core_action G M 6 hMindex
  let K : Subgroup G := MonoidHom.ker ψ
  have hKdvd : Nat.card K ∣ 35 := by
    rw [← hM]
    exact Subgroup.card_dvd_of_le hkerle
  have hKprod : Nat.card K * K.index = 210 := by
    simpa [K, Nat.card_eq_fintype_card, hG] using K.card_mul_index
  have hKindexDvd : K.index ∣ 720 := by
    change (MonoidHom.ker ψ).index ∣ 720
    rw [Subgroup.index_ker]
    have hrange := ψ.range.card_subgroup_dvd_card
    have hp : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_perm]
      norm_num
    rw [hp] at hrange
    exact hrange
  rcases apm_b98a01_core_card_arithmetic (Nat.card K) K.index
      hKdvd hKprod hKindexDvd with hK | hK
  · exact ⟨K, inferInstance, hK⟩
  · exact apm_b98a01_normal_order7_of_normal_order35 G K inferInstance hK

/-- The repaired order-thirty-five condition is equivalent to the existence
of a normal subgroup of order seven. -/
lemma apm_b98a01_order35_iff_normal_order7
    (G : Type*) [Group G] [Fintype G] (hG : Fintype.card G = 210) :
    (∃ M : Subgroup G, Nat.card M = 35) ↔
      ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7 := by
  constructor
  · rintro ⟨M, hM⟩
    exact apm_b98a01_normal_order7_of_order35 G M hG hM
  · rintro ⟨N, hNnormal, hN⟩
    exact apm_b98a01_order35_of_normal_order7 G N hG hNnormal hN

/-- An order-ten subgroup can be conjugated to one containing any prescribed
order-five subgroup.  Inside it, that subgroup has index two and is normal. -/
lemma apm_b98a01_order10_over_order5
    (G : Type*) [Group G] [Fintype G] (B L : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5) (hL : Nat.card L = 10) :
    ∃ L' : Subgroup G, Nat.card L' = 10 ∧ B ≤ L' ∧ (B.subgroupOf L').Normal := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 L := default
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hL, Nat.factorization_def 10 (by norm_num : Nat.Prime 5),
      show 10 = 5 * 2 by norm_num,
      padicValNat_base_mul (p := 5) (n := 2) (by norm_num) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let Q : Subgroup G := (P : Subgroup L).map L.subtype
  have hQcard : Nat.card Q = 5 := by
    change Nat.card ((P : Subgroup L).map L.subtype) = 5
    exact (Nat.card_congr
      ((P : Subgroup L).equivMapOfInjective L.subtype Subtype.coe_injective).toEquiv).symm.trans
        hPcard
  let Qs : Sylow 5 G := apm_b98a01_orderFiveSylow G Q hG hQcard
  let Bs : Sylow 5 G := apm_b98a01_orderFiveSylow G B hG hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Qs Bs
  let L' : Subgroup G := L.map (MulAut.conj g).toMonoidHom
  have hL' : Nat.card L' = 10 := by
    change Nat.card (L.map (MulAut.conj g).toMonoidHom) = 10
    exact (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g) L).toEquiv).symm.trans hL
  have hQB : Q.map (MulAut.conj g).toMonoidHom = B := by
    exact congr_arg Sylow.toSubgroup hg
  have hQL : Q ≤ L := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hBL' : B ≤ L' := by
    rw [← hQB]
    exact Subgroup.map_mono hQL
  refine ⟨L', hL', hBL', ?_⟩
  apply Subgroup.normal_of_index_eq_two
  have hp := (B.subgroupOf L').card_mul_index
  have hsubcard : Nat.card (B.subgroupOf L') = 5 := by
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL').toEquiv).trans hB
  rw [hsubcard, hL'] at hp
  omega

/-- An order-thirty-five subgroup can likewise be conjugated to contain the
prescribed order-five subgroup; Sylow arithmetic makes it normal there. -/
lemma apm_b98a01_order35_over_order5
    (G : Type*) [Group G] [Fintype G] (B M : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5) (hM : Nat.card M = 35) :
    ∃ M' : Subgroup G, Nat.card M' = 35 ∧ B ≤ M' ∧ (B.subgroupOf M').Normal := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let P : Sylow 5 M := default
  have hPcard : Nat.card P = 5 := by
    rw [P.card_eq_multiplicity, hM, Nat.factorization_def 35 (by norm_num : Nat.Prime 5),
      show 35 = 5 * 7 by norm_num,
      padicValNat_base_mul (p := 5) (n := 7) (by norm_num) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  let Q : Subgroup G := (P : Subgroup M).map M.subtype
  have hQcard : Nat.card Q = 5 := by
    change Nat.card ((P : Subgroup M).map M.subtype) = 5
    exact (Nat.card_congr
      ((P : Subgroup M).equivMapOfInjective M.subtype Subtype.coe_injective).toEquiv).symm.trans
        hPcard
  let Qs : Sylow 5 G := apm_b98a01_orderFiveSylow G Q hG hQcard
  let Bs : Sylow 5 G := apm_b98a01_orderFiveSylow G B hG hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Qs Bs
  let M' : Subgroup G := M.map (MulAut.conj g).toMonoidHom
  have hM' : Nat.card M' = 35 := by
    change Nat.card (M.map (MulAut.conj g).toMonoidHom) = 35
    exact (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj g) M).toEquiv).symm.trans hM
  have hQB : Q.map (MulAut.conj g).toMonoidHom = B := by
    exact congr_arg Sylow.toSubgroup hg
  have hQM : Q ≤ M := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  have hBM' : B ≤ M' := by
    rw [← hQB]
    exact Subgroup.map_mono hQM
  let Bs' : Sylow 5 M' := by
    apply Sylow.ofCard (B.subgroupOf M')
    rw [show Nat.card (B.subgroupOf M') = 5 by
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM').toEquiv).trans hB, hM',
      Nat.factorization_def 35 (by norm_num : Nat.Prime 5),
      show 35 = 5 * 7 by norm_num,
      padicValNat_base_mul (p := 5) (n := 7) (by norm_num) (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  have hBindex : (B.subgroupOf M').index = 7 := by
    have hp := (B.subgroupOf M').card_mul_index
    rw [show Nat.card (B.subgroupOf M') = 5 by
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM').toEquiv).trans hB, hM'] at hp
    omega
  let s := Nat.card (Sylow 5 M')
  have hsdvd : s ∣ 7 := by
    simpa [s, Bs', hBindex] using Bs'.card_dvd_index
  have hsmod : s % 5 = 1 := by
    have hm := card_sylow_modEq_one 5 M'
    change s % 5 = 1 % 5 at hm
    simpa using hm
  have hs : s = 1 := by
    have hspos : 0 < s := Nat.card_pos
    have hsle : s ≤ 7 := Nat.le_of_dvd (by norm_num) hsdvd
    interval_cases s
    all_goals norm_num at *
  letI : Subsingleton (Sylow 5 M') := (Nat.card_eq_one_iff_unique.mp hs).1
  refine ⟨M', hM', hBM', ?_⟩
  have hnormal : (Bs' : Subgroup M').Normal := Bs'.normal_of_subsingleton
  simpa [Bs'] using hnormal

lemma apm_b98a01_order10_forces_normalizer10
    (G : Type*) [Group G] [Fintype G] (B : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5) (hnormal : ¬B.Normal)
    (h10 : ∃ L : Subgroup G, Nat.card L = 10) :
    Nat.card (Subgroup.normalizer (B : Set G)) = 10 := by
  obtain ⟨L, hL⟩ := h10
  obtain ⟨L', hL', hBL', hBnormal⟩ := apm_b98a01_order10_over_order5 G B L hG hB hL
  have hle : L' ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBL').mp hBnormal
  have hdvd : 10 ∣ Nat.card (Subgroup.normalizer (B : Set G)) := by
    rw [← hL']
    exact Subgroup.card_dvd_of_le hle
  rcases apm_b98a01_orderFive_normalizer_card G B hG hB hnormal with h | h
  · exact h
  · norm_num [h] at hdvd

lemma apm_b98a01_order35_forces_normalizer35
    (G : Type*) [Group G] [Fintype G] (B : Subgroup G)
    (hG : Fintype.card G = 210) (hB : Nat.card B = 5) (hnormal : ¬B.Normal)
    (h35 : ∃ M : Subgroup G, Nat.card M = 35) :
    Nat.card (Subgroup.normalizer (B : Set G)) = 35 := by
  obtain ⟨M, hM⟩ := h35
  obtain ⟨M', hM', hBM', hBnormal⟩ := apm_b98a01_order35_over_order5 G B M hG hB hM
  have hle : M' ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBM').mp hBnormal
  have hdvd : 35 ∣ Nat.card (Subgroup.normalizer (B : Set G)) := by
    rw [← hM']
    exact Subgroup.card_dvd_of_le hle
  rcases apm_b98a01_orderFive_normalizer_card G B hG hB hnormal with h | h
  · norm_num [h] at hdvd
  · exact h

theorem apm_b98a01 :
    (∀ (G : Type*) [Group G] [Fintype G] (H : Subgroup G) (n : ℕ),
      H.index = n →
      ∃ ψ : G →* Equiv.Perm (Fin n),
        MonoidHom.ker ψ ≤ H ∧
        ∀ N : Subgroup G, N.Normal → N ≤ H → N ≤ MonoidHom.ker ψ) ∧
    (∀ (G : Type*) [Group G] [Fintype G] (B : Subgroup G),
      Fintype.card G = 210 →
      Nat.card B = 5 →
      ¬B.Normal →
      (Nat.card (Subgroup.normalizer (B : Set G)) = 10 ∨
        Nat.card (Subgroup.normalizer (B : Set G)) = 35) ∧
      ((∃ L : Subgroup G, Nat.card L = 10) →
        Nat.card (Subgroup.normalizer (B : Set G)) = 10) ∧
      (((∃ L : Subgroup G, Nat.card L = 10) ∧
          ¬∃ M : Subgroup G, Nat.card M = 35) ∨
        ((∃ M : Subgroup G, Nat.card M = 35) ∧
          ¬∃ L : Subgroup G, Nat.card L = 10)) ∧
      ((∃ M : Subgroup G, Nat.card M = 35) ↔
        ∃ N : Subgroup G, N.Normal ∧ Nat.card N = 7)) := by
  /-
  Boundary (pass-1 Codex, skipped): Mathlib packages the conceptual engine of
  part (a): `Subgroup.normalCore_eq_ker` identifies the kernel of the coset
  action, and `Subgroup.normal_le_normalCore` expresses its universal property
  for normal subgroups. A proof still has to choose an equivalence from
  the quotient `G ⧸ H` to `Fin n` from the index equality and conjugate the
  permutation representation along it.

  For part (b), source search found general Sylow tools including
  `Sylow.card_eq_index_normalizer` and `Sylow.card_sylow_modEq_one`, but no
  order-210 specialization or proved sibling. Closing the frozen conjunction
  requires showing the arbitrary order-5 subgroup `B` is Sylow, enumerating the
  divisors of 42 congruent to 1 modulo 5, converting the resulting normalizer
  indices to the exact cardinal alternatives 10 and 35, and transporting those
  sizes across conjugate Sylow subgroups.

  Closer hop 1 closes the entire numerical enumeration in two compiled
  helpers. `apm_b98a01_sylow5_count_arithmetic` proves that any nontrivial
  divisor of `42` congruent to `1` modulo `5` is `6` or `21`.
  `apm_b98a01_normalizer_card_arithmetic` then converts the group-order
  product equation into normalizer cardinality `10` or `35`. Thus the
  remaining first-alternative bridge is purely group-theoretic: show an
  arbitrary order-five `B` is Sylow, obtain the standard divisibility and
  congruence facts, and relate Sylow count to the normalizer product.

  The final equivalence additionally
  needs the index-six core action, divisibility of its quotient order into
  `6!`, elimination of kernel sizes 1, 5, and 35, and construction of the
  converse order-35 subgroup from a normal order-7 subgroup. These bridges are
  not available as packaged lemmas. Renewed searches of `LEMMA-INDEX.md`, the
  closed corpus, `ConstructionTargets/`, Sylow, core, and coset-action APIs
  found no packaged order-210 bridge. The repaired statement appears sound.

  Closer hop 2 closes the entire first normalizer-cardinality alternative.
  `apm_b98a01_orderFiveSylow` uses `Sylow.ofCard` after computing the
  five-adic factorization of `210`; `apm_b98a01_orderFive_index` proves the
  subgroup index is `42`. `apm_b98a01_orderFive_normalizer_card` then combines
  `Sylow.card_dvd_index`, `card_sylow_modEq_one`, nonnormality via
  `Sylow.normal_of_subsingleton`, `Sylow.card_eq_index_normalizer`, and
  `Subgroup.card_mul_index` with the hop-1 arithmetic helpers to obtain
  normalizer cardinality `10` or `35`. Part (a), the exclusivity/refinement
  clauses, and the order-35/normal-order-7 equivalence still require the
  coset/core action and subgroup constructions described above.

  Closer hop 3 closes part (a) completely in
  `apm_b98a01_coset_core_action`.  It transports the canonical action on
  `G ⧸ H` through `Fintype.equivFinOfCardEq`, identifies the transported
  kernel with `H.normalCore`, and applies `normal_le_normalCore` for the
  universal property.  The main theorem now wires both this clause and the
  hop-2 normalizer alternative explicitly; only the refinement/exclusivity
  clauses and order-35/normal-order-7 equivalence remain.

  Solver round 1 adds the constructive reverse implication in the final
  equivalence.  Given a normal order-seven subgroup, the quotient has order
  thirty; Cauchy's theorem supplies an order-five cyclic subgroup there, and
  its preimage has index six and hence order thirty-five.  The forward
  implication still depends on extracting the order-seven normal core from an
  index-six subgroup.

  Solver rounds 2--3 close the remaining chain.  Kernel divisibility in the
  index-six action yields the normal order-seven subgroup and proves the final
  equivalence.  Conjugating a Sylow-five subgroup of any order-ten or
  order-thirty-five subgroup onto `B` embeds a subgroup of the corresponding
  size in `normalizer B`; the Sylow-five subgroup is normal in the conjugated
  container (by index two in the first case and Sylow counting in the second).
  Thus the normalizer dichotomy determines which size exists and proves both
  refinement and exclusivity.
  -/
  refine ⟨fun G _ _ H n hn => apm_b98a01_coset_core_action G H n hn, ?_⟩
  intro G _ _ B hG hB hnormal
  have hnc := apm_b98a01_orderFive_normalizer_card G B hG hB hnormal
  refine ⟨hnc, ?_⟩
  refine ⟨apm_b98a01_order10_forces_normalizer10 G B hG hB hnormal, ?_⟩
  refine ⟨?_, apm_b98a01_order35_iff_normal_order7 G hG⟩
  rcases hnc with hnc10 | hnc35
  · left
    refine ⟨⟨Subgroup.normalizer (B : Set G), hnc10⟩, ?_⟩
    rintro ⟨M, hM⟩
    have h := apm_b98a01_order35_forces_normalizer35 G B hG hB hnormal ⟨M, hM⟩
    omega
  · right
    refine ⟨⟨Subgroup.normalizer (B : Set G), hnc35⟩, ?_⟩
    rintro ⟨L, hL⟩
    have h := apm_b98a01_order10_forces_normalizer10 G B hG hB hnormal ⟨L, hL⟩
    omega
