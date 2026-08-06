import Mathlib

/-!
# APM b99A02

## Statement repairs

None.

## Encoding questions

None.
-/

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
  constructor
  · exact Sylow.normal_of_subsingleton P
  /-
  Boundary after the compiled first Sylow count:
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
  -/
  sorry
