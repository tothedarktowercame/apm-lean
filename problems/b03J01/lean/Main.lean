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
  · -- Boundary (closer hop 1): bridge still open. Enriched route with API names.
    -- Proof chain (6 steps, ~60-90 lines total):
    -- 1. |G| = p*(p+2), p and p+2 distinct primes → Squarefree |G|
    -- 2. Squarefree → IsZGroup G (by `IsZGroup.of_squarefree`)
    -- 3. For each prime q | |G|: `Sylow.card_sylow_modEq_one` gives n_q ≡ 1 (mod q),
    --    `Sylow.card_dvd_index` gives n_q | (|G|/q). Twin-prime arithmetic ⟹ n_q = 1.
    -- 4. n_q = 1 ⟹ Sylow q G is Subsingleton ⟹ `(↑P : Subgroup G).Normal`
    -- 5. All Sylows normal ⟹ `Group.IsNilpotent G` (by `isNilpotent_of_finite_tfae` #4)
    -- 6. `[IsZGroup G] [Group.IsNilpotent G]` ⟹ `IsCyclic G` (instance in ZGroup.lean:125)
    --
    -- Key APIs: `Sylow.card_sylow_modEq_one`, `Sylow.not_dvd_card_sylow`,
    -- `IsZGroup.of_squarefree` (ZGroup.lean:57), `isCyclic` instance (ZGroup.lean:125),
    -- `isNilpotent_of_finite_tfae` (Nilpotent.lean:941)
    sorry
