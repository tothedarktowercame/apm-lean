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
  · -- Boundary: exhaustive pass-1 desk research found the intended chain in
    -- Mathlib: `Sylow.card_sylow_modEq_one`, `Sylow.card_dvd_index`,
    -- `Sylow.normal_of_subsingleton`, `isNilpotent_of_finite_tfae`,
    -- `IsZGroup.of_squarefree`, and the nilpotent `IsZGroup` cyclic instance.
    -- The remaining route is to derive that the cardinality of each Sylow type
    -- is one from `|G| = p * (p + 2)` and the twin-prime arithmetic, install
    -- normality for every prime divisor, and feed those instances through the
    -- nilpotence/Z-group chain.
    --
    -- I also scanned all 160 closed problem artifacts, all modules in
    -- `ConstructionTargets/`, `YoungL2.lean`, and the partial group neighbors
    -- `b93A01`, `b90A01`, and `b96A02`.  The construction libraries are
    -- analytic and irrelevant here; the group neighbors stop at the same
    -- Sylow-cardinality/typeclass plumbing.  No packaged order-`p*q`
    -- classification or reusable completed proof was found, and I did not
    -- complete that plumbing within this pass.
    sorry
