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
import ConstructionTargets.PointWedgeVanKampen

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

/-- The distinguished point in the concrete second point-wedge. -/
def T99J01ThreeCirclesPoint : ThreeCircles :=
  ConstructionTargets.PointWedgeQuotient.quotientMap twoCirclesPoint 1
    (Sum.inl twoCirclesPoint)

/-- The circle group in the rank-one free-group coordinates used by the two
successive point-wedge computations. -/
theorem t99J01_circle_fundamentalGroup :
    Nonempty (FundamentalGroup Circle 1 ≃* FreeGroup (Fin 1)) := by
  sorry

/-- The first concrete specialization of point-wedge van Kampen. -/
theorem t99J01_twoCircles_fundamentalGroup_coprod :
    Nonempty (FundamentalGroup TwoCircles twoCirclesPoint ≃*
      Monoid.Coprod (FundamentalGroup Circle 1) (FundamentalGroup Circle 1)) := by
  sorry

/-- Algebraic conversion of the first van Kampen coproduct to rank two.  Both
geometric inputs are hypotheses so this leaf is independent of them. -/
-- BEGIN SEAT AREA
theorem t99J01_twoCircles_fundamentalGroup_freeGroup
    (hcircle : Nonempty (FundamentalGroup Circle 1 ≃* FreeGroup (Fin 1)))
    (hwedge : Nonempty (FundamentalGroup TwoCircles twoCirclesPoint ≃*
      Monoid.Coprod (FundamentalGroup Circle 1) (FundamentalGroup Circle 1))) :
    Nonempty (FundamentalGroup TwoCircles twoCirclesPoint ≃* FreeGroup (Fin 2)) := by
  sorry
-- END SEAT AREA

/-- The second concrete specialization of point-wedge van Kampen. -/
theorem t99J01_threeCircles_fundamentalGroup_coprod :
    Nonempty (FundamentalGroup ThreeCircles T99J01ThreeCirclesPoint ≃*
      Monoid.Coprod (FundamentalGroup TwoCircles twoCirclesPoint)
        (FundamentalGroup Circle 1)) := by
  sorry

/-- Algebraic conversion of the second van Kampen coproduct to rank three.
All earlier conclusions are explicit hypotheses, so this is a parallel leaf. -/
theorem t99J01_threeCircles_wedgePoint_fundamentalGroup
    (hcircle : Nonempty (FundamentalGroup Circle 1 ≃* FreeGroup (Fin 1)))
    (htwo : Nonempty
      (FundamentalGroup TwoCircles twoCirclesPoint ≃* FreeGroup (Fin 2)))
    (hwedge : Nonempty (FundamentalGroup ThreeCircles T99J01ThreeCirclesPoint ≃*
      Monoid.Coprod (FundamentalGroup TwoCircles twoCirclesPoint)
        (FundamentalGroup Circle 1))) :
    Nonempty (FundamentalGroup ThreeCircles T99J01ThreeCirclesPoint ≃*
      FreeGroup (Fin 3)) := by
  sorry

/-- Basepoint transport, isolated from both van Kampen specializations. -/
theorem t99J01_threeCircles_basepoint_transport (x : ThreeCircles) :
    Nonempty (FundamentalGroup ThreeCircles x ≃*
      FundamentalGroup ThreeCircles T99J01ThreeCirclesPoint) := by
  sorry

/-- The iterated point-wedge model used by the problem has free fundamental
group on three generators, at every basepoint. -/
theorem t99J01_threeCircles_fundamentalGroup
    (x : ThreeCircles) :
    Nonempty (FundamentalGroup ThreeCircles x ≃* FreeGroup (Fin 3)) := by
  obtain ⟨hcircle⟩ := t99J01_circle_fundamentalGroup
  obtain ⟨htwoWedge⟩ := t99J01_twoCircles_fundamentalGroup_coprod
  obtain ⟨htwo⟩ := t99J01_twoCircles_fundamentalGroup_freeGroup
    ⟨hcircle⟩ ⟨htwoWedge⟩
  obtain ⟨hthreeWedge⟩ := t99J01_threeCircles_fundamentalGroup_coprod
  obtain ⟨hthree⟩ := t99J01_threeCircles_wedgePoint_fundamentalGroup
    ⟨hcircle⟩ ⟨htwo⟩ ⟨hthreeWedge⟩
  obtain ⟨htransport⟩ := t99J01_threeCircles_basepoint_transport x
  exact ⟨htransport.trans hthree⟩

/-- The cyclic pullback of the degree-`n` circle map along collapse to the
first circle is a connected `n`-sheeted cover. -/
theorem t99J01_exists_connected_cover
    (n : ℕ) (hn : 0 < n) :
    ∃ (E : Type) (_ : TopologicalSpace E) (p : E → ThreeCircles),
      PathConnectedSpace E ∧ IsKSheetedCover p n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let E := ConstructionTargets.CyclicThreeCirclesPullbackCover.Pullback n
  let p : E → ThreeCircles :=
    ConstructionTargets.CyclicThreeCirclesPullbackCover.projection n
  exact ⟨E, inferInstance, p,
    ConstructionTargets.CyclicThreeCirclesPullbackPathConnected.pullbackPathConnectedSpace n,
    ConstructionTargets.CyclicThreeCirclesPullbackSheets.pullback_isKSheeted n⟩

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
noncomputable instance
    t99J01_arbitrary_cover_component_aux_restricted_cover_aux_sphereLocPathConnected :
    LocPathConnectedSpace (ConstructionTargets.SphereHomology.Sphere 1) :=
  ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 1))
    (ConstructionTargets.SphereHomology.Sphere 1)

noncomputable instance
    t99J01_arbitrary_cover_component_aux_restricted_cover_aux_circleLocPathConnected :
    LocPathConnectedSpace Circle :=
  Topology.IsQuotientMap.locPathConnectedSpace
    ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.symm.isQuotientMap

noncomputable instance
    t99J01_arbitrary_cover_component_aux_restricted_cover_aux_circlePathConnected :
    PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using h)

noncomputable instance
    t99J01_arbitrary_cover_component_aux_restricted_cover_aux_twoCirclesPathConnected :
    PathConnectedSpace TwoCircles := inferInstance

noncomputable instance
    t99J01_arbitrary_cover_component_aux_restricted_cover_aux_twoCirclesLocPathConnected :
    LocPathConnectedSpace TwoCircles :=
  Topology.IsQuotientMap.locPathConnectedSpace
    (show Topology.IsQuotientMap
        (ConstructionTargets.PointWedgeQuotient.quotientMap (1 : Circle) (1 : Circle)) from
      ⟨ConstructionTargets.PointWedgeQuotient.surjective_quotientMap _ _, rfl⟩)

noncomputable instance
    t99J01_arbitrary_cover_component_aux_restricted_cover_aux_threeCirclesLocPathConnected :
    LocPathConnectedSpace ThreeCircles :=
  Topology.IsQuotientMap.locPathConnectedSpace
    (show Topology.IsQuotientMap
        (ConstructionTargets.PointWedgeQuotient.quotientMap twoCirclesPoint (1 : Circle)) from
      ⟨ConstructionTargets.PointWedgeQuotient.surjective_quotientMap _ _, rfl⟩)

noncomputable instance
    t99J01_arbitrary_cover_component_aux_restricted_cover_aux_threeCirclesPathConnected :
    PathConnectedSpace ThreeCircles := inferInstance

def t99J01_arbitrary_cover_component_aux_restricted_cover_aux_fiberEmbedding
    {E : Type} [TopologicalSpace E] (p : E → ThreeCircles) (e : E)
    (b : ThreeCircles) :
    {z : ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentAt e //
      ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentCoverMap p e z = b} ↪
      {x : E // p x = b} where
  toFun z := ⟨z.1.1, z.2⟩
  inj' z w h := by
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun u : {x : E // p x = b} ↦ u.1) h

def t99J01_arbitrary_cover_component_aux_restricted_cover_aux_baseFiberEquiv
    {E : Type} [TopologicalSpace E] (p : E → ThreeCircles) (e : E) :
    {z : ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentAt e //
      ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentCoverMap p e z = p e} ≃
      {x : E // p x = p e ∧ Joined e x} where
  toFun z := ⟨z.1.1, z.2, z.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv z := by rfl
  right_inv x := by rfl

theorem t99J01_arbitrary_cover_component_aux_restricted_cover
    (E : Type) [TopologicalSpace E] (n : ℕ) (p : E → ThreeCircles)
    (hp : IsKSheetedCover p n) (e : E) :
    IsKSheetedCover
      (ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentCoverMap p e)
      (T99J01ComponentSheets p e) := by
  let q :=
    ConstructionTargets.T99J01PathComponentCoverRestriction.t99j01ComponentCoverMap p e
  have hq :=
    ConstructionTargets.RestrictPathComponent.IsCoveringMap.restrictPathComponent
      hp.isCoveringMap e
  refine {
    isCoveringMap := hq.1
    finite_fiber := ?_
    card_fiber := ?_ }
  · intro b
    letI : Finite {x : E // p x = b} := hp.finite_fiber b
    exact Finite.of_injective
      (t99J01_arbitrary_cover_component_aux_restricted_cover_aux_fiberEmbedding p e b)
      (t99J01_arbitrary_cover_component_aux_restricted_cover_aux_fiberEmbedding p e b).injective
  · intro b
    obtain ⟨γ⟩ := PathConnectedSpace.joined (p e) b
    let γq : Path.Homotopic.Quotient (p e) b := Quotient.mk'' γ
    let fiberEquiv : (q ⁻¹' {p e}) ≃ (q ⁻¹' {b}) :=
      Equiv.ofBijective (hq.1.monodromy γq) (hq.1.monodromy_bijective γq)
    calc
      Nat.card {z // q z = b} = Nat.card {z // q z = p e} :=
        (Nat.card_congr fiberEquiv).symm
      _ = Nat.card {x : E // p x = p e ∧ Joined e x} :=
        Nat.card_congr
          (t99J01_arbitrary_cover_component_aux_restricted_cover_aux_baseFiberEquiv p e)
      _ = T99J01ComponentSheets p e := rfl

/-- Missing from the advertised component-restriction construction target. -/
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
