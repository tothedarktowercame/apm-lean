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
  sorry
