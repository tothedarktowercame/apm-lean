import Mathlib

/-!
# APM b97J01 — solvable and nilpotent groups; finite p-groups

## Statement repairs

None.

## Encoding notes

Solvability and nilpotence are defined using the derived and lower central
series, respectively.  The requested examples are the explicit groups `S₅`
and `S₃`, represented as permutation groups on `Fin 5` and `Fin 3`.
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
  /-
  Boundary (pass-1 Codex, skipped): Mathlib directly supplies the large-group
  and p-group ingredients: `Equiv.Perm.fin_5_not_solvable`,
  `IsPGroup.of_card`, `IsPGroup.bot_lt_center`, `IsPGroup.isNilpotent`, and
  `nilpotent_iff_lowerCentralSeries`. These bridge the first, fourth, and fifth
  conjuncts to the statement's explicit series definitions after routine
  `Fintype.card`/`Nat.card` and `Fact p.Prime` conversions.

  Local source and proved-sibling searches found no packaged results for the
  two concrete `Equiv.Perm (Fin 3)` conjuncts. Closing them requires either
  explicit computations proving `derivedSeries _ 2 = ⊥` and showing the lower
  central series stalls, or a formal self-normalizing proper subgroup combined
  with `normalizerCondition_of_isNilpotent`. The subgroup closures in these
  series are not exposed by the searched API as finite decidable tables, and no
  sibling contains the needed `S₃` computation. The statement appears
  mathematically sound; the blocker is this concrete finite-group bridge.
  -/
  sorry
