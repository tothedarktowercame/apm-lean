import Mathlib

noncomputable section

/-!
# APM b01A02

## Statement repairs

None.

## Encoding notes

The order and subgroup index are the actual finite cardinality and
`Subgroup.index`. Normality and cyclicity use Mathlib's structural predicates,
rather than merely asserting numerical consequences of them.
-/

def apmSmallestPrimeDivisor (p n : ℕ) : Prop :=
  p.Prime ∧ p ∣ n ∧ ∀ q : ℕ, q.Prime → q ∣ n → p ≤ q

theorem apm_b01a02 :
    (∀ (G : Type*) [Group G] [Fintype G]
      (p : ℕ) (H : Subgroup G),
      apmSmallestPrimeDivisor p (Fintype.card G) →
      H.index = p → H.Normal) ∧
    (∀ (G : Type*) [Group G] [Fintype G],
      Fintype.card G = 255 →
        (∃ P : Subgroup G, P.Normal ∧ Nat.card P = 17) ∧
        (∃ H : Subgroup G,
          H.Normal ∧ Nat.card H = 85 ∧ IsCyclic H) ∧
        IsCyclic G) := by
  sorry
