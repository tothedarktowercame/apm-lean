import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.CoveringDegree
import ConstructionTargets.T99J01PathComponentCoverRestriction
import ConstructionTargets.T99J01ComponentSheetBounds
import ConstructionTargets.CyclicThreeCirclesPullbackSheets
import ConstructionTargets.CyclicThreeCirclesPullbackPathConnected
import ConstructionTargets.CyclicThreeCirclesPullbackCover
import ConstructionTargets.FiniteIndexFreeGroupSchreierRank
import ConstructionTargets.T99J01CoverSubgroupIndex

/-! # t99J01: finite covers of a wedge of three circles

The four lemmas below isolate the geometric construction, the one large van
Kampen computation, the connected-cover Schreier argument, and the reduction
of an arbitrary cover to the path component of a chosen point.
-/

open ConstructionTargets.StatementSurfaceModels ConstructionTargets.CoveringDegree

noncomputable section

/-- Sheets in the component containing `e`, measured over its image in the base. -/
def T99J01ComponentSheets {E : Type} [TopologicalSpace E]
    (p : E → ThreeCircles) (e : E) : ℕ :=
  Nat.card {x : E // p x = p e ∧ Joined e x}

/-- **LIBRARY.** The iterated point-wedge model used by the problem has free
fundamental group on three generators, at every basepoint. -/
theorem t99J01_threeCircles_fundamentalGroup
    (x : ThreeCircles) :
    Nonempty (FundamentalGroup ThreeCircles x ≃* FreeGroup (Fin 3)) := by
  sorry

/-- The cyclic pullback of the degree-`n` circle map along collapse to the
first circle is a connected `n`-sheeted cover. -/
theorem t99J01_exists_connected_cover
    (n : ℕ) (hn : 0 < n) :
    ∃ (E : Type) (_ : TopologicalSpace E) (p : E → ThreeCircles),
      PathConnectedSpace E ∧ IsKSheetedCover p n := by
  sorry

/-- A connected finite cover is the subgroup corresponding to one fiber
orbit.  Its index is the sheet count, and finite-index Schreier gives rank
`2*n+1`.  The base-group computation is supplied as a hypothesis so this
lemma can be proved independently of the LIBRARY lemma. -/
-- BEGIN SEAT AREA
theorem t99J01_connected_cover_fundamentalGroup
    (hbase : ∀ x : ThreeCircles,
      Nonempty (FundamentalGroup ThreeCircles x ≃* FreeGroup (Fin 3)))
    (E : Type) [TopologicalSpace E] [PathConnectedSpace E]
    (n : ℕ) (p : E → ThreeCircles) (hp : IsKSheetedCover p n) (e : E) :
    Nonempty (FundamentalGroup E e ≃* FreeGroup (Fin (2 * n + 1))) := by
  let f := ConstructionTargets.coveringInducedFundamentalGroupMap hp.isCoveringMap e
  obtain ⟨base⟩ := hbase (p e)
  let H : Subgroup (FreeGroup (Fin 3)) := f.range.map base.toMonoidHom
  have hn : 0 < n := by
    rw [← hp.card_fiber (p e)]
    letI : Finite {x : E // p x = p e} := hp.finite_fiber (p e)
    letI : Nonempty {x : E // p x = p e} := ⟨⟨e, rfl⟩⟩
    exact Nat.card_pos
  have hindex : H.index = n := by
    calc
      H.index = f.range.index := Subgroup.index_map_equiv f.range base
      _ = n := (t99j01_cover_pi1_subgroup_index n p hp e).2
  obtain ⟨schreier⟩ :=
    FiniteIndexFreeGroupSchreierRank.indexSubgroupFreeGroupFinThreeEquiv
      n hn H hindex
  refine ⟨?_⟩
  exact
    (MonoidHom.ofInjective (t99j01_cover_pi1_subgroup_index n p hp e).1).trans
      ((Subgroup.equivMapOfInjective f.range base.toMonoidHom base.injective).trans schreier)
-- END SEAT AREA

/-- Restrict a cover to the path component through `e`.  That restriction is
a connected finite cover whose degree is exactly `T99J01ComponentSheets`, and
its fundamental group agrees with that of the ambient total space at `e`.
The connected-cover conclusion is supplied as a hypothesis so this component
lemma can be assigned in parallel with the connected Schreier lemma. -/
theorem t99J01_arbitrary_cover_component
    (hconnected : ∀ (E : Type) [TopologicalSpace E] [PathConnectedSpace E]
      (n : ℕ) (p : E → ThreeCircles), IsKSheetedCover p n →
      ∀ e : E,
        Nonempty (FundamentalGroup E e ≃* FreeGroup (Fin (2 * n + 1))))
    (E : Type) [TopologicalSpace E] (n : ℕ) (p : E → ThreeCircles)
    (hp : IsKSheetedCover p n) (e : E) :
    0 < T99J01ComponentSheets p e ∧ T99J01ComponentSheets p e ≤ n ∧
      Nonempty (FundamentalGroup E e ≃*
        FreeGroup (Fin (2 * T99J01ComponentSheets p e + 1))) := by
  sorry

theorem apm_t99j01 :
    (∀ n : ℕ, 0 < n → ∃ (E : Type) (_ : TopologicalSpace E)
      (p : E → ThreeCircles), PathConnectedSpace E ∧ IsKSheetedCover p n) ∧
    (∀ (E : Type) [TopologicalSpace E] [PathConnectedSpace E]
      (n : ℕ) (p : E → ThreeCircles), IsKSheetedCover p n →
      ∀ e : E, Nonempty (FundamentalGroup E e ≃* FreeGroup (Fin (2 * n + 1)))) ∧
    (∀ (E : Type) [TopologicalSpace E] (n : ℕ) (p : E → ThreeCircles),
      IsKSheetedCover p n → ∀ e : E,
      0 < T99J01ComponentSheets p e ∧ T99J01ComponentSheets p e ≤ n ∧
      Nonempty (FundamentalGroup E e ≃*
        FreeGroup (Fin (2 * T99J01ComponentSheets p e + 1)))) := by
  let hbase := t99J01_threeCircles_fundamentalGroup
  let hconnected := t99J01_connected_cover_fundamentalGroup hbase
  exact ⟨t99J01_exists_connected_cover, hconnected,
    t99J01_arbitrary_cover_component hconnected⟩

#print axioms apm_t99j01
