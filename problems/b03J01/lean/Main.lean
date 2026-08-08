import Mathlib

noncomputable section

/-!
# APM b03J01

## Statement repairs

None.

## Encoding notes

Group order and subgroup index are encoded by actual finite cardinality and
`Subgroup.index`; normality and cyclicity use their structural predicates.
-/

def apmB03SmallestPrimeDivisor (p n : ℕ) : Prop :=
  p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q

lemma apm_b03J01_twinPrime_squarefree (p : ℕ) (hp : p.Prime)
    (hp2 : (p + 2).Prime) : Squarefree (p * (p + 2)) := by
  apply (Nat.squarefree_mul ((Nat.coprime_primes hp hp2).2 (by omega))).2
  exact ⟨hp.squarefree, hp2.squarefree⟩

lemma apm_b03J01_isZGroup_of_twinPrime_card
    (G : Type*) [Group G] [Fintype G] (p : ℕ) (hp : p.Prime)
    (hp2 : (p + 2).Prime) (hcard : Fintype.card G = p * (p + 2)) :
    IsZGroup G := by
  apply IsZGroup.of_squarefree
  rw [Nat.card_eq_fintype_card, hcard]
  exact apm_b03J01_twinPrime_squarefree p hp hp2

lemma apm_b03J01_sylow_normal_of_not_dvd_card
    (G : Type*) [Group G] [Fintype G] (q : ℕ) (hq : q.Prime)
    (hqdvd : ¬q ∣ Fintype.card G) (Q : Sylow q G) :
    (↑Q : Subgroup G).Normal := by
  letI : Fact q.Prime := ⟨hq⟩
  have hcardQ : Nat.card Q = 1 := by
    rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd]
    · exact pow_zero q
    · simpa [Nat.card_eq_fintype_card] using hqdvd
  have hbot : (↑Q : Subgroup G) = ⊥ :=
    (Q : Subgroup G).eq_bot_of_card_eq hcardQ
  rw [hbot]
  infer_instance

/-- Why this unblocks `apm_b03j01`: Sylow congruence and divisibility for a
group of order `p * (p + 2)` force every Sylow count to be one.  Packaging
that arithmetic as `Subsingleton (Sylow q G)` is exactly the hypothesis of
`Sylow.normal_of_subsingleton`, after which the standard all-Sylows-normal
criterion gives nilpotence and the existing `IsZGroup` instance gives
cyclicity. -/
theorem apm_b03J01_bridge_sylow_subsingleton_of_twinPrime_card
    (G : Type*) [Group G] [Fintype G]
    (p q : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hq : q.Prime)
    (hcard : Fintype.card G = p * (p + 2)) :
    Subsingleton (Sylow q G) := by
  sorry

theorem apm_b03j01
    (G : Type*) [Group G] [Fintype G]
    (p : ℕ) (H : Subgroup G)
    (hp : apmB03SmallestPrimeDivisor p (Fintype.card G))
    (hindex : H.index = p) :
    H.Normal ∧
      ((p + 2).Prime → Fintype.card G = p * (p + 2) → IsCyclic G) := by
  rcases hp with ⟨hpprime, hpdiv, hpmin⟩
  have hcard_ne_one : Fintype.card G ≠ 1 := by
    intro hcard
    rw [hcard] at hpdiv
    exact hpprime.not_dvd_one hpdiv
  have hminfac : (Fintype.card G).minFac = p := by
    apply Nat.le_antisymm
    · exact Nat.minFac_le_of_dvd hpprime.two_le hpdiv
    · apply hpmin (Fintype.card G).minFac
      · exact Nat.minFac_prime hcard_ne_one
      · exact Nat.minFac_dvd (Fintype.card G)
  refine ⟨?_, ?_⟩
  · apply H.normal_of_index_eq_minFac_card
    simpa [Nat.card_eq_fintype_card, hminfac] using hindex
  · intro hp2 hcard
    letI : IsZGroup G :=
      apm_b03J01_isZGroup_of_twinPrime_card G p hpprime hp2 hcard
    -- Boundary (closer hop 2): bridge still open after closing steps 1--2.
    -- Proved locally above: |G| = p*(p+2), with both factors prime, is squarefree;
    -- hence `IsZGroup.of_squarefree` supplies `[IsZGroup G]` here.
    -- Remaining proof chain:
    -- 3. For each prime q | |G|: `Sylow.card_sylow_modEq_one` gives n_q ≡ 1 (mod q),
    --    `Sylow.card_dvd_index` gives n_q | (|G|/q). Twin-prime arithmetic ⟹ n_q = 1.
    -- 4. n_q = 1 ⟹ Sylow q G is Subsingleton ⟹ `(↑P : Subgroup G).Normal`
    -- 5. All Sylows normal ⟹ `Group.IsNilpotent G` (by `isNilpotent_of_finite_tfae` #4)
    -- 6. `[IsZGroup G] [Group.IsNilpotent G]` ⟹ `IsCyclic G` (instance in ZGroup.lean:125)
    --
    -- Key APIs: `Sylow.card_sylow_modEq_one`, `Sylow.not_dvd_card_sylow`,
    -- `IsZGroup.of_squarefree` (ZGroup.lean:57), `isCyclic` instance (ZGroup.lean:125),
    -- `isNilpotent_of_finite_tfae` (Nilpotent.lean:941)
    -- New attempts: searched the closed corpus and `LEMMA-INDEX.md` for a theorem
    -- classifying groups of twin-prime order, and Mathlib for a direct
    -- `IsZGroup`-to-`IsNilpotent` bridge; neither exists. The remaining quantified
    -- Sylow argument must split q | p*(p+2) into q=p or q=p+2, prove uniqueness
    -- from the two cardinality lemmas, and transport it to `Subgroup.Normal`.
    -- Closer hop 3 closes the previously omitted branch for primes not dividing
    -- `|G|`: `apm_b03J01_sylow_normal_of_not_dvd_card` uses
    -- `Sylow.card_eq_multiplicity` and
    -- `Nat.factorization_eq_zero_of_not_dvd` to identify the Sylow subgroup
    -- with `⊥`. For the two dividing primes, no direct order-`pq`
    -- classification theorem was found. The remaining branch still needs the
    -- explicit arithmetic on `Nat.card (Sylow q G)` from
    -- `card_sylow_modEq_one` and `card_dvd_index`, followed by construction of
    -- the `Subsingleton (Sylow q G)` instance required by
    -- `Sylow.normal_of_subsingleton`.
    sorry
