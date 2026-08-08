import Mathlib

/-!
# APM b97J01 — solvable and nilpotent groups; finite p-groups

Solvability and nilpotence use Mathlib's standard derived series and lower
central series.  The examples are the concrete permutation groups `S₅` and
`S₃`, and the final clauses are the usual center and nilpotence theorems for
finite groups of prime-power order.

## Statement repairs

None.

## Encoding questions

None.
-/

def apm_b97j01_solvable (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, derivedSeries G n = ⊥

def apm_b97j01_nilpotent (G : Type) [Group G] : Prop :=
  ∃ n : ℕ, lowerCentralSeries G n = ⊥

theorem apm_b97j01 :
    ¬apm_b97j01_solvable (Equiv.Perm (Fin 5)) ∧
    apm_b97j01_solvable (Equiv.Perm (Fin 3)) ∧
    ¬apm_b97j01_nilpotent (Equiv.Perm (Fin 3)) ∧
    (∀ (G : Type) [Group G] [Fintype G] (p n : ℕ),
      p.Prime → Fintype.card G = p ^ n → 1 < p ^ n →
        Subgroup.center G ≠ ⊥) ∧
    (∀ (G : Type) [Group G] [Fintype G] (p n : ℕ),
      p.Prime → Fintype.card G = p ^ n →
        apm_b97j01_nilpotent G) := by
  sorry
