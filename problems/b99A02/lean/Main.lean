import Mathlib

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
    native_decide
  have hSindex : S.index = 7 := by
    have h := S.toSubgroup.index_mul_card
    rw [hScard, hX] at h
    omega
  have hdvd : Nat.card (Sylow 29 X) ∣ 7 := by
    simpa [hSindex] using Sylow.card_dvd_index S
  have hnmem : Nat.card (Sylow 29 X) ∈ Nat.divisors 7 :=
    Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hdivs : Nat.divisors 7 = {1, 7} := by native_decide
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
    native_decide
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
    have hdivs : Nat.divisors 203 = {1, 7, 29, 203} := by native_decide
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
    native_decide
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
  /-
  Boundary after closer hop 1 and the compiled first Sylow count:
  `Sylow.card_eq_multiplicity`, `Sylow.card_dvd_index`, and
  `card_sylow_modEq_one` prove that there is exactly one Sylow
  `5`-subgroup, so `Sylow.normal_of_subsingleton` closes `P.Normal`.
  The remaining cascade must form `G ⩸ P`, construct its normal Sylow
  `29`-subgroup, pull it back to a normal subgroup `H` of cardinality
  `5^2 * 29`, and then transport uniqueness back to the specified `Q`.
  Searches found the individual quotient, `Subgroup.comap`, cardinality, and
  characteristic/normality APIs, but no compiled sibling or packaged theorem
  combining those transports.  The final subgroup `K = P R` additionally
  needs product-cardinality bookkeeping and the reverse implication from
  `K.Normal` to commutativity via all three normal Sylows.

  New progress: `apm_b99A02_normal_comap_mk_and_le` packages the exact
  correspondence-theorem step needed after finding the quotient Sylow:
  for normal `S ≤ G ⩸ P`, its comap is normal in `G` and contains `P`.
  This uses `Subgroup.Normal.comap` and `QuotientGroup.le_comap_mk'`.
  The remaining bridge for `H` is therefore confined to proving uniqueness of
  the Sylow `29`-subgroup in the quotient and establishing the comap cardinal
  `25 * 29`; the latter can be approached through
  `QuotientGroup.comapMk'OrderIso` plus `Subgroup.card_mul_index`.

  Closer hop 2 closes that cardinality bridge outright as
  `apm_b99A02_card_comap_mk`, using the more direct
  `QuotientGroup.card_preimage_mk`: for every `S ≤ G ⧸ N`, the comap has
  cardinality `Nat.card N * Nat.card S`. Thus once the quotient Sylow-29
  subgroup is constructed with cardinality 29, its normal pullback has the
  required cardinality `25 * 29` immediately. The remaining cascade is the
  quotient Sylow uniqueness count, transport of normality to the specified
  `Q`, and the final `K = P R` normality/commutativity equivalence.

  Closer hop 3 proves the quotient count as the reusable lemmas
  `apm_b99A02_sylow29_unique_of_card_203` and
  `apm_b99A02_sylow29_normal_of_card_203`. The main proof now computes
  `|G ⩸ P| = 203`, constructs its normal Sylow-29 subgroup, and pulls it back.
  Together with `apm_b99A02_card_comap_mk`, this closes the entire existence
  clause for a normal `H` of cardinality `5^2 * 29`. The sole remaining
  boundary is transporting the resulting Sylow-29 normality to the specified
  `Q`, then constructing `K = P R` and proving its normality/commutativity
  equivalence.
  -/
  sorry
