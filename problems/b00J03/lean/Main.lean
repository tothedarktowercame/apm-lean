import Mathlib

/-!
# APM b00J03

## Statement repairs

None.

## Encoding questions

None. Nonabelianness is stated by an explicit pair of noncommuting elements,
and `commutator G` is Mathlib's commutator subgroup `[G,G]`.
-/

theorem apm_b00j03 :
    ∀ (p : ℕ) (G : Type*) [Group G] [Fintype G],
      Nat.Prime p →
      Fintype.card G = p ^ 3 →
      (∃ x y : G, x * y ≠ y * x) →
      Nat.card (Subgroup.center G) = p ∧
        Subgroup.center G = commutator G := by
  sorry
