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
theorem t99J01_connected_cover_fundamentalGroup
    (hbase : ∀ x : ThreeCircles,
      Nonempty (FundamentalGroup ThreeCircles x ≃* FreeGroup (Fin 3)))
    (E : Type) [TopologicalSpace E] [PathConnectedSpace E]
    (n : ℕ) (p : E → ThreeCircles) (hp : IsKSheetedCover p n) (e : E) :
    Nonempty (FundamentalGroup E e ≃* FreeGroup (Fin (2 * n + 1))) := by
  sorry

/-- Restrict a cover to the path component through `e`.  That restriction is
a connected finite cover whose degree is exactly `T99J01ComponentSheets`, and
its fundamental group agrees with that of the ambient total space at `e`.
The connected-cover conclusion is supplied as a hypothesis so this component
lemma can be assigned in parallel with the connected Schreier lemma. -/
theorem t99J01_arbitrary_cover_component_aux_bounds
    (E : Type) [TopologicalSpace E] (n : ℕ) (p : E → ThreeCircles)
    (hp : IsKSheetedCover p n) (e : E) :
    0 < T99J01ComponentSheets p e ∧ T99J01ComponentSheets p e ≤ n := by
  constructor
  · exact ConstructionTargets.T99J01ComponentSheetBounds.componentFiberCard_pos hp e
  · exact ConstructionTargets.T99J01ComponentSheetBounds.componentFiberCard_le hp e

/-- Missing from the advertised component-restriction construction target. -/
theorem t99J01_arbitrary_cover_component_aux_restricted_cover
    (E : Type) [TopologicalSpace E] (n : ℕ) (p : E → ThreeCircles)
    (hp : IsKSheetedCover p n) (e : E) :
    IsKSheetedCover
      (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentCoverMap p e)
      (T99J01ComponentSheets p e) := by
  sorry

/-- Missing from the advertised component-restriction construction target. -/
-- BEGIN SEAT AREA
private def t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_path
    {E : Type} [TopologicalSpace E] {e : E} (p : Path e e) :
    Path
      (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentBase e)
      (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentBase e) where
  toFun t := ⟨p t, by
    show Joined e (p t)
    exact ⟨(p.subpath 0 t).cast p.source.symm rfl⟩⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

private def t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_homotopy
    {E : Type} [TopologicalSpace E] {e : E} {p q : Path e e}
    (F : p.Homotopy q) :
    (t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_path p).Homotopy
      (t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_path q) where
  toFun x := ⟨F x, by
    show Joined e (F x)
    exact ⟨((F.eval x.1).subpath 0 x.2).cast (F.eval x.1).source.symm rfl⟩⟩
  continuous_toFun := F.continuous.subtype_mk (fun x => by
    show Joined e (F x)
    exact ⟨((F.eval x.1).subpath 0 x.2).cast (F.eval x.1).source.symm rfl⟩)
  map_zero_left x := Subtype.ext (F.map_zero_left x)
  map_one_left x := Subtype.ext (F.map_one_left x)
  prop' t x hx := by
    apply Subtype.ext
    exact F.prop' t x hx

private theorem t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_bijective
    {E : Type} [TopologicalSpace E] (e : E) :
    Function.Bijective
      (FundamentalGroup.map
        (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentInclusion e)
        (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentBase e)) := by
  constructor
  · intro a b hab
    induction a using Path.Homotopic.Quotient.ind with
    | mk p =>
      induction b using Path.Homotopic.Quotient.ind with
      | mk q =>
        change (Path.Homotopic.Quotient.mk p).map _ =
          (Path.Homotopic.Quotient.mk q).map _ at hab
        rw [← Path.Homotopic.Quotient.mk_map,
          ← Path.Homotopic.Quotient.mk_map,
          Path.Homotopic.Quotient.eq] at hab
        change (Path.Homotopic.Quotient.mk p) = Path.Homotopic.Quotient.mk q
        rw [Path.Homotopic.Quotient.eq]
        rcases hab with ⟨F⟩
        refine ⟨Path.Homotopy.cast
          (t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_homotopy F) ?_ ?_⟩
        · ext t
          rfl
        · ext t
          rfl
  · intro a
    induction a using Path.Homotopic.Quotient.ind with
    | mk p =>
      refine ⟨Path.Homotopic.Quotient.mk
        (t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_path p), ?_⟩
      rfl

theorem t99J01_arbitrary_cover_component_aux_pi1_equiv
    (E : Type) [TopologicalSpace E] (e : E) :
    Nonempty
      (FundamentalGroup E e ≃*
        FundamentalGroup
          (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentAt e)
          (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentBase e)) := by
  exact ⟨(MulEquiv.ofBijective
    (FundamentalGroup.map
      (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentInclusion e)
      (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentBase e))
    (t99J01_arbitrary_cover_component_aux_pi1_equiv_aux_bijective e)).symm⟩
-- END SEAT AREA

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
  rcases t99J01_arbitrary_cover_component_aux_bounds E n p hp e with ⟨hpos, hle⟩
  refine ⟨hpos, hle, ?_⟩
  let C := ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentAt e
  let ce := ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentBase e
  let q := ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentCoverMap p e
  have hq : IsKSheetedCover q (T99J01ComponentSheets p e) :=
    t99J01_arbitrary_cover_component_aux_restricted_cover E n p hp e
  have hc := hconnected C (T99J01ComponentSheets p e) q hq ce
  rcases t99J01_arbitrary_cover_component_aux_pi1_equiv E e with ⟨hi⟩
  rcases hc with ⟨hc⟩
  exact ⟨hi.trans hc⟩

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
