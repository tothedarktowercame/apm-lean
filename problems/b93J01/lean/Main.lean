import Mathlib

/-!
# APM b93J01 — false group-theory assertions and their corrections

## Statement repairs

In item (c), the conclusion's `subgroup of order n` is corrected to
`subgroup of order m`; as printed, the whole group makes the assertion
trivially true and contradicts the instruction to show it false.

For item (e), the correction adds the standard condition `p ∤ q - 1`.

## Encoding questions

None. An abelian group being a direct sum of cyclic groups is encoded by a
family of cyclic subgroups which is independent and whose supremum is the
whole group.
-/

open scoped BigOperators

noncomputable section

def apm_b93J01_IsDirectSumOfCyclic (G : Type*) [AddCommGroup G] : Prop :=
  ∃ (ι : Type) (A : ι → AddSubgroup G),
    (∀ i, IsAddCyclic (A i)) ∧ iSupIndep A ∧ iSup A = ⊤

theorem apm_b93j01 :
    -- (a): `A₄` is a counterexample; `Aₙ` is simple for `n ≥ 5`.
    ¬IsSimpleGroup (alternatingGroup (Fin 4)) ∧
    (∀ n : ℕ, 5 ≤ n → IsSimpleGroup (alternatingGroup (Fin n))) ∧
    -- (b): `Q₈` is missing from the proposed list; there are five types.
    (Fintype.card (QuaternionGroup 2) = 8 ∧
      ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 8)) ∧
      ¬Nonempty (QuaternionGroup 2 ≃* Multiplicative (ZMod 4 × ZMod 2)) ∧
      ¬Nonempty (QuaternionGroup 2 ≃* DihedralGroup 4)) ∧
    (∀ (G : Type) [Group G] [Fintype G], Fintype.card G = 8 →
      Nonempty (G ≃* Multiplicative (ZMod 8)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 4 × ZMod 2)) ∨
      Nonempty (G ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) ∨
      Nonempty (G ≃* DihedralGroup 4) ∨
      Nonempty (G ≃* QuaternionGroup 2)) ∧
    -- (c): `A₄` has no subgroup of order six; Lagrange is the correction.
    (Fintype.card (alternatingGroup (Fin 4)) = 12 ∧
      ¬∃ H : Subgroup (alternatingGroup (Fin 4)), Nat.card H = 6) ∧
    (∀ (G : Type) [Group G] [Fintype G] (H : Subgroup G),
      Nat.card H ∣ Fintype.card G) ∧
    -- (d): `ℚ` is not such a direct sum; finite abelian groups are.
    ¬apm_b93J01_IsDirectSumOfCyclic ℚ ∧
    (∀ (G : Type) [AddCommGroup G] [Fintype G],
      apm_b93J01_IsDirectSumOfCyclic G) ∧
    -- (e): `S₃` has order `2·3` but is not cyclic; add `p ∤ q-1`.
    (Fintype.card (Equiv.Perm (Fin 3)) = 2 * 3 ∧
      ¬IsCyclic (Equiv.Perm (Fin 3))) ∧
    (∀ (p q : ℕ), Nat.Prime p → Nat.Prime q → p < q → (¬p ∣ (q - 1)) →
      ∀ (G : Type) [Group G] [Fintype G], Fintype.card G = p * q →
        IsCyclic G) := by
  sorry
