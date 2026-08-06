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
  sorry
