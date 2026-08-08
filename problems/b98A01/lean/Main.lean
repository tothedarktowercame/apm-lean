import Mathlib

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
  have hf : Nat.factorization 210 5 = 1 := by native_decide
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
  -/
  refine ⟨fun G _ _ H n hn => apm_b98a01_coset_core_action G H n hn, ?_⟩
  intro G _ _ B hG hB hnormal
  refine ⟨apm_b98a01_orderFive_normalizer_card G B hG hB hnormal, ?_⟩
  sorry
