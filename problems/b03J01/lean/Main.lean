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
  · -- Boundary: searched `Sylow.card_sylow_modEq_one`,
    -- `Sylow.card_dvd_index`, `Sylow.normal_of_subsingleton`, and
    -- `IsZGroup.of_squarefree`.  The remaining route is to show both Sylow
    -- subgroups are unique from the twin-prime arithmetic, obtain nilpotence,
    -- and invoke the cyclicity theorem for finite squarefree nilpotent groups.
    -- I did not complete the required Sylow-cardinality/index API plumbing.
    sorry
