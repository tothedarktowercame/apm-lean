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

lemma apm_t00j08_rank_seven_realizable :
    ∃ G : Subgroup (FreeGroup (Fin 7)),
      G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7)) := by
  refine ⟨⊤, ?_, ⟨Subgroup.topEquiv⟩⟩
  infer_instance

lemma apm_t00j08_rank_zero_impossible :
    ¬∃ G : Subgroup (FreeGroup (Fin 0)),
      G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7)) := by
  rintro ⟨G, _, ⟨e⟩⟩
  have hamb : ∀ z : FreeGroup (Fin 0), z = 1 := by
    intro z
    induction z using FreeGroup.induction_on with
    | C1 => rfl
    | of x => exact Fin.elim0 x
    | inv_of x _ => exact Fin.elim0 x
    | mul x y hx hy => simp [hx, hy]
  have hsub : ∀ x y : G, x = y := by
    intro x y
    apply Subtype.ext
    rw [hamb x.1, hamb y.1]
  have heq : FreeGroup.of (0 : Fin 7) = FreeGroup.of (1 : Fin 7) := by
    apply e.symm.injective
    exact hsub _ _
  exact Fin.zero_ne_one (FreeGroup.of_injective heq)

lemma apm_t00j08_rank_one_impossible :
    ¬∃ G : Subgroup (FreeGroup (Fin 1)),
      G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7)) := by
  rintro ⟨G, _, ⟨e⟩⟩
  have hcomm :
      FreeGroup.of (0 : Fin 7) * FreeGroup.of (1 : Fin 7) =
        FreeGroup.of (1 : Fin 7) * FreeGroup.of (0 : Fin 7) := by
    calc
      FreeGroup.of (0 : Fin 7) * FreeGroup.of (1 : Fin 7) =
          e (e.symm (FreeGroup.of (0 : Fin 7)) *
            e.symm (FreeGroup.of (1 : Fin 7))) := by simp
      _ = e (e.symm (FreeGroup.of (1 : Fin 7)) *
            e.symm (FreeGroup.of (0 : Fin 7))) := by rw [mul_comm]
      _ = FreeGroup.of (1 : Fin 7) * FreeGroup.of (0 : Fin 7) := by simp
  have hnoncomm :
      FreeGroup.of (0 : Fin 7) * FreeGroup.of (1 : Fin 7) ≠
        FreeGroup.of (1 : Fin 7) * FreeGroup.of (0 : Fin 7) := by
    decide
  exact hnoncomm hcomm

theorem apm_t00j08 :
    ∀ n : ℕ,
      (∃ G : Subgroup (FreeGroup (Fin n)),
        G.FiniteIndex ∧ Nonempty (G ≃* FreeGroup (Fin 7))) ↔
      n ∈ ({2, 3, 4, 7} : Set ℕ) := by
  have hseven := apm_t00j08_rank_seven_realizable
  /-
  Boundary (closer hop 2): realizability of the rank-seven ambient case is
  now a reusable compiled lemma, `apm_t00j08_rank_seven_realizable`.
  The new lemma `apm_t00j08_rank_zero_impossible` also excludes `n = 0`
  directly: induction shows `FreeGroup (Fin 0)` is trivial, whereas
  `FreeGroup.of_injective` distinguishes two generators of rank seven.
  The new lemma `apm_t00j08_rank_one_impossible` excludes `n = 1` without
  any rank formula: `FreeGroup (Fin 1)` is cyclic, hence its subgroups are
  commutative, while `decide` certifies that the first two canonical
  generators of `FreeGroup (Fin 7)` do not commute. Thus an isomorphism is
  impossible.

  Mathlib contains the qualitative
  Nielsen--Schreier theorem `subgroupIsFreeOfIsFree`, and Schreier's lemma for
  finite generation, but I found no finite-index rank formula computing the
  cardinality of a free basis:
  `rank G - 1 = [F : G] * (rank F - 1)`. The existing groupoid proof does not
  expose the finite spanning-tree edge count needed to derive this equation.
  I also inspected `Subgroup.exists_finset_card_le_mul` and
  `Subgroup.rank_le_index_mul_rank` in Mathlib's `Schreier.lean`. They give
  only the upper bound `rank G ≤ [F : G] * rank F`, not the sharp
  subtraction-by-one equality, so they cannot exclude the remaining ranks.
  The closed sibling `b95J01` uses `Subgroup.card_mul_index` successfully for
  a finite ambient group, but that cardinality argument gives no rank equation
  for an infinite free group. No relevant result occurs in
  `ConstructionTargets/` or `YoungL2.lean`. A renewed search of the free-group
  groupoid/spanning-tree source found no cardinality theorem for its resulting
  basis. Constructing the other three examples and excluding `n ≥ 1` outside
  `{2,3,4,7}` therefore still requires a new quantitative Nielsen--Schreier
  development.
  -/
  sorry
