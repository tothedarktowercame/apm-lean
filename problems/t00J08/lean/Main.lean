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
  have hseven : ∃ G : Subgroup (FreeGroup (Fin 7)),
      G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7)) := by
    refine ⟨⊤, ?_, ⟨Subgroup.topEquiv⟩⟩
    infer_instance
  /-
  Boundary: realizability of the rank-seven ambient case is proved above by
  taking the whole free group. Mathlib contains the qualitative
  Nielsen--Schreier theorem `subgroupIsFreeOfIsFree`, and Schreier's lemma for
  finite generation, but I found no finite-index rank formula computing the
  cardinality of a free basis:
  `rank G - 1 = [F : G] * (rank F - 1)`. The existing groupoid proof does not
  expose the finite spanning-tree edge count needed to derive this equation.
  Constructing the other three examples and excluding all remaining `n`
  therefore requires a new quantitative Nielsen--Schreier development.
  -/
  sorry
