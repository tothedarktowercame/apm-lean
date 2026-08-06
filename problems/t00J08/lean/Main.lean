import Mathlib

/-!
# APM t00J08

## Statement repairs

None.

## Encoding questions

Following the problem's intended Nielsen–Schreier reading, "`G` contains 7
free generators" means that `G` itself is free of rank seven, encoded by a
group isomorphism with `FreeGroup (Fin 7)`. Finite index uses Mathlib's
`Subgroup.FiniteIndex` predicate.
-/

theorem apm_t00j08 :
    ∀ n : ℕ,
      (∃ G : Subgroup (FreeGroup (Fin n)),
        G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7))) ↔
      n ∈ ({2, 3, 4, 7} : Set ℕ) := by
  sorry
