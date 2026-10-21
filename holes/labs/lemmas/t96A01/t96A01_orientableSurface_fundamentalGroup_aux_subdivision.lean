import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.PolygonSurfacePiOne
import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.PolygonCellPiOne
import ConstructionTargets.SurfaceClassification
import ConstructionTargets.CoveringDegree
import ConstructionTargets.CoveringMonodromyCosets
import ConstructionTargets.SuppliedCoverAlgebra
import ConstructionTargets.CoveringSubgroupCorrespondence

/-! # Blueprint for t96A01: finite-index subgroups of a genus-four surface group -/

open ConstructionTargets.StatementSurfaceModels ConstructionTargets.Surfaces
open ConstructionTargets.CoveringSubgroupCorrespondence

noncomputable section

/-! ## Definitions shared by the independent lemma seats -/

/-- The canonical interior basepoint of the standard orientable polygon surface. -/
abbrev T96A01SurfaceBase (g : ℕ) : Surface true g :=
  surfacePoint true g

/-! ## Independent library interfaces -/

open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology in
/-- Leaf (generic; copy of the `hn` step in `t91A02_polygon_pi1_wedge_quotient`,
holes/labs/blueprints/t91A02/Blueprint.lean).  The cell-attachment boundary class
`wordClass P` and the polygon boundary class have the same normal closure:
`wordClass P` is the integer-loop class, which is the fundamental class to the
power `circleIntegerLoopOneCoordinate = ±1`. -/
theorem t96A01_orientableSurface_fundamentalGroup_aux_wordClass (P : PairingData) :
    Subgroup.normalClosure
        ({ConstructionTargets.PolygonCellPiOne.wordClass P} : Set _) =
      Subgroup.normalClosure ({polygonBoundaryFundamentalClass P} : Set _) := by
  classical
  have hw : ConstructionTargets.PolygonCellPiOne.wordClass P =
      Path.Homotopic.Quotient.mk
        (polygonBoundaryIntegerLoopPath P) := by
    simp only [ConstructionTargets.PolygonCellPiOne.wordClass,
      ConstructionTargets.AttachTwoCell.loopClassAt,
      ConstructionTargets.PolygonCellPiOne.bword,
      polygonBoundaryIntegerLoopPath,
      circleIntegerLoopOneClass, FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map]
    rw [Path.Homotopic.Quotient.mk_cast]
  rw [hw, polygonBoundaryIntegerLoopClass_eq_fundamental_zpow_coordinate]
  rcases circleIntegerLoopOneCoordinate_eq_one_or_neg_one with h | h
  · rw [h]
    simp
  · rw [h]
    simp only [zpow_neg, zpow_one]
    apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      intro y hy
      rcases hy with rfl
      exact Subgroup.inv_mem _
        (Subgroup.subset_normalClosure (Set.mem_singleton _))
    · apply Subgroup.normalClosure_le_normal
      intro y hy
      rcases hy with rfl
      have hi := Subgroup.inv_mem
        (Subgroup.normalClosure
          ({(polygonBoundaryFundamentalClass P)⁻¹} : Set _))
        (Subgroup.subset_normalClosure (Set.mem_singleton _))
      simpa using hi

open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology in
/-- Leaf (geometric subdivision, for the standard orientable data).  The boundary
loop of the polygon, read in the orbit wedge, is the ordered product of its signed
edge classes.  `PolygonSurfaceHomology.lean` calls this "the remaining geometric
subdivision theorem" (docstring of `polygonBoundaryExplicitEdgeProduct`) and has
consumers taking it as a hypothesis (`polygonBoundaryWedgeLoop_hurewicz_of_eq_explicitEdgeProduct`).
Compare `t97A01Closure.torusRP2AttachingWord`, which does this for one pairing. -/
-- BEGIN SEAT AREA
theorem t96A01_orientableSurface_fundamentalGroup_aux_subdivision
    (g : ℕ) (hg : 0 < g) :
    polygonBoundaryFundamentalClass (standardPairingData true g hg) =
      polygonBoundaryExplicitEdgeProduct (standardPairingData true g hg) := by
  sorry
-- END SEAT AREA

open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology in
/-- Leaf (combinatorial relabelling).  Some isomorphism of free groups carries the
standard commutator word `surfaceRelator g` to a word whose leg class normally
generates the same subgroup as the explicit edge product of
`orientableStandardPairingData` (read off how that data labels its `4g` edges;
a conjugate, cyclic rotation, or inverse of the relator is fine). -/
noncomputable def t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_inv
    (A : Type*) : FreeGroup A ≃* FreeGroup A where
  toFun := FreeGroup.lift fun a => (FreeGroup.of a)⁻¹
  invFun := FreeGroup.lift fun a => (FreeGroup.of a)⁻¹
  map_mul' := map_mul _
  left_inv x := by
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of a => simp
    | inv_of a h => simp
    | mul x y hx hy => simp only [map_mul, hx, hy]
  right_inv x := by
    induction x using FreeGroup.induction_on with
    | C1 => simp
    | of a => simp
    | inv_of a h => simp
    | mul x y hx hy => simp only [map_mul, hx, hy]

open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology

def t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_castHom
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y) :
    FundamentalGroup X y →* FundamentalGroup X x where
  toFun q := Path.Homotopic.Quotient.cast q h h
  map_one' := by subst y; rfl
  map_mul' a b := by
    subst y
    induction a using Quotient.inductionOn with
    | _ a => induction b using Quotient.inductionOn with | _ b => rfl

lemma t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_explicit
    (P : ConstructionTargets.PolygonSurfacePiOne.PairingData)
    (l : ConstructionTargets.PolygonSurfacePiOne.PairingOrbit P.pair) :
    ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase P l =
      ConstructionTargets.PolygonSurfaceHomology.finiteWedgeLegFundamentalClassAtBase P l ^
        ConstructionTargets.PolygonSurfaceHomology.circleIntegerLoopOneCoordinate := by
  simp only [ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClassAtBase,
    ConstructionTargets.PolygonSurfaceHomology.finiteWedgeLegFundamentalClassAtBase,
    ConstructionTargets.PolygonSurfaceHomology.finiteWedgeExplicitLegClass_eq_positive_zpow]
  exact map_zpow
    (t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_castHom
      (ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient.wedgeCircle_base_eq
        (P.orbit ⟨0, P.edgeCount_pos⟩) l)) _ _

lemma t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_blocks
    {G : Type*} [Group G] (g : ℕ) (x : Fin g × Bool → G) :
    (List.ofFn fun i : Fin (4 * g) =>
      let c := ConstructionTargets.PolygonSurfacePiOne.orientableCoord g i
      if ConstructionTargets.PolygonSurfacePiOne.handleSign c.2 then x (c.1, ConstructionTargets.PolygonSurfacePiOne.handleOrbitLabel c.2)
      else (x (c.1, ConstructionTargets.PolygonSurfacePiOne.handleOrbitLabel c.2))⁻¹).prod =
    (List.ofFn fun a : Fin g =>
      (x (a, false))⁻¹ * (x (a, true))⁻¹ * x (a, false) * x (a, true)).prod := by
  rw [List.ofFn_mul']
  simp only [List.prod_flatten, List.map_ofFn]
  apply congrArg List.prod
  apply List.ofFn_inj.mpr
  apply funext
  intro i
  change (List.ofFn fun j : Fin 4 =>
    let c := ConstructionTargets.PolygonSurfacePiOne.orientableCoord g
      ⟨4 * i + j, by omega⟩
    if ConstructionTargets.PolygonSurfacePiOne.handleSign c.2 then
      x (c.1, ConstructionTargets.PolygonSurfacePiOne.handleOrbitLabel c.2)
    else (x (c.1, ConstructionTargets.PolygonSurfacePiOne.handleOrbitLabel c.2))⁻¹).prod = _
  have hc (j : Fin 4) :
      ConstructionTargets.PolygonSurfacePiOne.orientableCoord g
        ⟨4 * (i : ℕ) + (j : ℕ), by omega⟩ = (i, j) := by
    apply Prod.ext <;> apply Fin.ext <;>
      simp [ConstructionTargets.PolygonSurfacePiOne.orientableCoord,
        Fin.divNat, Fin.modNat] <;> omega
  simp only [hc]
  simp [ConstructionTargets.PolygonSurfacePiOne.handleSign,
    ConstructionTargets.PolygonSurfacePiOne.handleOrbitLabel, Fin.modNat,
    Nat.add_comm, mul_assoc, hc]

theorem t96A01_orientableSurface_fundamentalGroup_aux_relabel
    (g : ℕ) (hg : 0 < g) :
    ∃ M : FreeGroup (Fin g × Bool) ≃*
        FreeGroup (PairingOrbit (standardPairingData true g hg).pair),
      Subgroup.normalClosure
          ({ConstructionTargets.PolygonCellPiOne.legEquiv
              (standardPairingData true g hg) (M (surfaceRelator g))} : Set _) =
        Subgroup.normalClosure
          ({polygonBoundaryExplicitEdgeProduct (standardPairingData true g hg)} :
            Set _) := by
  classical
  let P := standardPairingData true g hg
  let e : PairingOrbit P.pair ≃ Fin g × Bool := orientableOrbitEquiv g
  let x : Fin g × Bool → FundamentalGroup
      (PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair)) (orbitWedgeBase P) :=
    fun p => finiteWedgeLegFundamentalClassAtBase P (e.symm p)
  have hlab (i : Fin (4 * g)) :
      finiteWedgeLegFundamentalClassAtBase P (P.orbit i) = x (orientableOrbitLabel g i) := by
    have h : e (P.orbit i) = orientableOrbitLabel g i := rfl
    simp only [x, ← h, Equiv.symm_apply_apply]
  have hprod (s : ℤ) (hs : circleIntegerLoopOneCoordinate = s) :
      polygonBoundaryExplicitEdgeProduct P =
        (List.ofFn fun a : Fin g =>
          (x (a, false) ^ s)⁻¹ * (x (a, true) ^ s)⁻¹ * x (a, false) ^ s *
            x (a, true) ^ s).prod := by
    rw [← t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_blocks g
      (fun p => x p ^ s)]
    change (List.ofFn fun i : Fin (4 * g) => polygonBoundaryExplicitEdgeClass P i).prod = _
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    have hsign : P.sign i = handleSign (orientableCoord g i).2 := rfl
    simp only [polygonBoundaryExplicitEdgeClass,
      t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_explicit, hs, hlab, hsign]
    rfl
  have hleg (Q : ConstructionTargets.PolygonSurfacePiOne.PairingData) (q : PairingOrbit Q.pair) :
      ConstructionTargets.PolygonCellPiOne.legEquiv Q (FreeGroup.of q) =
        finiteWedgeLegFundamentalClassAtBase Q q := by
    change finiteWedgeLegFreeGroupMap Q (FreeGroup.of q) = _
    simp [finiteWedgeLegFreeGroupMap]
  rcases circleIntegerLoopOneCoordinate_eq_one_or_neg_one with hs | hs
  · refine ⟨(t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_inv _).trans
      (FreeGroup.freeGroupCongr e.symm), ?_⟩
    rw [hprod 1 hs]
    congr 2
    simp only [surfaceRelator, map_list_prod, List.map_ofFn, Function.comp_def, map_mul,
      map_inv, MulEquiv.trans_apply, zpow_one]
    simp [t96A01_orientableSurface_fundamentalGroup_aux_relabel_aux_inv,
      FreeGroup.freeGroupCongr_apply, x]
    exact congrArg List.prod (congrArg List.ofFn (funext fun a => by
      rw [hleg, hleg]))
  · refine ⟨FreeGroup.freeGroupCongr e.symm, ?_⟩
    rw [hprod (-1) hs]
    congr 2
    simp only [surfaceRelator, map_list_prod, List.map_ofFn, Function.comp_def, map_mul,
      map_inv, zpow_neg, zpow_one, inv_inv]
    simp [FreeGroup.freeGroupCongr_apply, x]
    exact congrArg List.prod (congrArg List.ofFn (funext fun a => by
      rw [hleg, hleg]))

open ConstructionTargets.PolygonSurfacePiOne ConstructionTargets.PolygonSurfaceHomology in
/-- Positive genus: `polygon_piOne_presentation` on the standard orientable data,
transported along `standardPairingData_space_homeomorph`. -/
theorem t96A01_orientableSurface_fundamentalGroup_aux_relator
    (g : ℕ) (hg : 0 < g) :
    Nonempty
      (FundamentalGroup (Surface true g) (T96A01SurfaceBase g) ≃*
        OrientableSurfaceGroup g) := by
  let P := standardPairingData true g hg
  obtain ⟨M, hM⟩ := t96A01_orientableSurface_fundamentalGroup_aux_relabel g hg
  have hr : Subgroup.normalClosure
        ({ConstructionTargets.PolygonCellPiOne.legEquiv P (M (surfaceRelator g))} :
          Set _) =
      Subgroup.normalClosure {ConstructionTargets.PolygonCellPiOne.wordClass P} := by
    rw [hM, ← t96A01_orientableSurface_fundamentalGroup_aux_subdivision g hg,
      t96A01_orientableSurface_fundamentalGroup_aux_wordClass P]
  obtain ⟨e⟩ := ConstructionTargets.PolygonCellPiOne.polygon_piOne_presentation
    P M (surfaceRelator g) hr
  let h := standardPairingData_space_homeomorph true g hg
  haveI : PathConnectedSpace (Surface true g) :=
    h.surjective.pathConnectedSpace h.continuous
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      (T96A01SurfaceBase g) (h P.center)).trans
    (((fundamentalGroupEquivOfHomeomorphEq h P.center (h P.center) rfl).symm.trans e))⟩

theorem t96A01_orientableSurface_fundamentalGroup_aux_homeomorph_of_fibres
    {Z X Y : Type*} [TopologicalSpace Z] [TopologicalSpace X]
    [TopologicalSpace Y] {p : Z → X} {q : Z → Y}
    (hp : Topology.IsQuotientMap p) (hq : Topology.IsQuotientMap q)
    (h : ∀ x y, p x = p y ↔ q x = q y) : Nonempty (X ≃ₜ Y) := by
  let p' : C(Z, X) := ⟨p, hp.continuous⟩
  let q' : C(Z, Y) := ⟨q, hq.continuous⟩
  have hker : Setoid.ker p' = Setoid.ker q' :=
    Setoid.ext fun x y ↦ h x y
  have e₁ := Topology.IsQuotientMap.homeomorph (f := p') hp
  have e₂ := Topology.IsQuotientMap.homeomorph (f := q') hq
  rw [hker] at e₁
  exact ⟨e₁.symm.trans e₂⟩

theorem t96A01_orientableSurface_fundamentalGroup_aux_zero
    (x : Surface true 0) :
    Subsingleton (FundamentalGroup (Surface true 0) x) := by
  have hrel (a b : ConstructionTargets.Surfaces.Disk) :
      Relation.EqvGen (ConstructionTargets.Surfaces.SurfaceRel true 0) a b ↔
        a = b := by
    constructor
    · intro h
      induction h with
      | rel a b hab =>
          simp [ConstructionTargets.Surfaces.SurfaceRel] at hab
      | refl a => rfl
      | symm a b _ ih => exact ih.symm
      | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    · rintro rfl
      exact Relation.EqvGen.refl _
  have he : Nonempty
      (ConstructionTargets.Surfaces.Disk ≃ₜ Surface true 0) :=
    t96A01_orientableSurface_fundamentalGroup_aux_homeomorph_of_fibres
      (p := id) (q := ConstructionTargets.Surfaces.surfaceQuotient true 0)
      Topology.IsQuotientMap.id
      ⟨ConstructionTargets.Surfaces.surjective_surfaceQuotient true 0, rfl⟩
      (fun a b => by
        change a = b ↔ Quotient.mk _ a = Quotient.mk _ b
        rw [Quotient.eq]
        change a = b ↔ Relation.EqvGen
          (ConstructionTargets.Surfaces.SurfaceRel true 0) a b
        exact (hrel a b).symm)
  letI : ContractibleSpace ConstructionTargets.Surfaces.Disk :=
    Convex.contractibleSpace (convex_closedBall (0 : ℂ) 1)
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  let e := Classical.choice he
  letI : ContractibleSpace (Surface true 0) := e.symm.contractibleSpace
  letI : SimplyConnectedSpace (Surface true 0) :=
    SimplyConnectedSpace.ofContractible _
  change Subsingleton (Path.Homotopic.Quotient x x)
  infer_instance

/-- **LIBRARY (polygon-surface fundamental group).**  The standard orientable
genus-`g` polygon quotient has the usual one-relator surface group. -/
theorem t96A01_orientableSurface_fundamentalGroup (g : ℕ) :
    Nonempty
      (FundamentalGroup (Surface true g) (T96A01SurfaceBase g) ≃*
        OrientableSurfaceGroup g) := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · letI := t96A01_orientableSurface_fundamentalGroup_aux_zero
      (T96A01SurfaceBase 0)
    letI : Unique
        (FundamentalGroup (Surface true 0) (T96A01SurfaceBase 0)) :=
      ⟨⟨1⟩, fun x ↦ Subsingleton.elim x 1⟩
    letI : Unique (FreeGroup (Fin 0 × Bool)) := inferInstance
    letI : Subsingleton (OrientableSurfaceGroup 0) :=
      ⟨fun x y ↦ Quotient.inductionOn₂ x y
        (fun a b ↦ congrArg (QuotientGroup.mk' _) (Subsingleton.elim a b))⟩
    letI : Unique (OrientableSurfaceGroup 0) :=
      ⟨⟨1⟩, fun x ↦ Subsingleton.elim x 1⟩
    exact ⟨MulEquiv.ofUnique⟩
  · exact t96A01_orientableSurface_fundamentalGroup_aux_relator g hg

/-- Finite index rules out Mathlib's `index = 0` sentinel. -/
theorem t96A01_index_pos
    {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    (n : ℕ) (hindex : H.index = n) :
    0 < n := by
  rw [← hindex]
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

/- **LIBRARY (covering-subgroup correspondence).**  A finite-index subgroup
is realized as the fundamental group of a connected cover whose fibre has the
prescribed cardinality. -/
/-- Surface charts give semilocally simply connected neighbourhoods.  No
`IsManifold` regularity is needed: this is a purely topological chart fact. -/
theorem t96A01_surface_semilocallySimplyConnected
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] :
    SemilocallySimplyConnected S := by
  intro x
  let e := chartAt (EuclideanSpace ℝ (Fin 2)) x
  have hxsource : x ∈ e.source := mem_chart_source _ x
  have hxtarget : e x ∈ e.target := e.map_source hxsource
  obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp e.open_target (e x) hxtarget
  let B : Set (EuclideanSpace ℝ (Fin 2)) := Metric.ball (e x) r
  let U : Set S := e.symm '' B
  have hBsub : B ⊆ e.symm.source := by
    simpa [B] using hrsub
  have hU_nhds : U ∈ nhds x := by
    have hB_nhds : B ∈ nhds (e x) := Metric.ball_mem_nhds _ hr
    have him := e.symm.image_mem_nhds hxtarget hB_nhds
    simpa [U, e, e.left_inv hxsource] using him
  refine ⟨U, hU_nhds, fun γ hγ ↦ ?_⟩
  let h : B ≃ₜ U := e.symm.homeomorphOfImageSubsetSource hBsub rfl
  letI : ContractibleSpace B :=
    (convex_ball (e x) r).contractibleSpace ⟨e x, by simpa [B] using hr⟩
  letI : ContractibleSpace U := h.symm.contractibleSpace
  letI : SimplyConnectedSpace U := inferInstance
  have hxU : x ∈ U := hγ ⟨0, Path.source γ⟩
  let xU : U := ⟨x, hxU⟩
  let γU : Path xU xU := {
    toFun := fun t ↦ (⟨γ t, hγ ⟨t, rfl⟩⟩ : U)
    continuous_toFun := (Path.continuous γ).subtype_mk _
    source' := Subtype.ext (Path.source γ)
    target' := Subtype.ext (Path.target γ)
  }
  have hhom : γU.Homotopic (Path.refl xU) :=
    SimplyConnectedSpace.paths_homotopic _ _
  let inc : C(U, S) := ⟨Subtype.val, continuous_subtype_val⟩
  have hmapped := hhom.map inc
  apply Path.Homotopic.Quotient.eq.mpr
  simpa [γU] using hmapped

/-- A compact surface is covered by finitely many chart sources, so it is the
image of a type in `Type`; this lets the cover be built in `Type` although `S`
lives in an arbitrary universe. -/
theorem t96A01_surface_small
    (S : Type*) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [CompactSpace S] :
    Small.{0} S := by
  classical
  let U : S → Set S := fun x ↦ (chartAt (EuclideanSpace ℝ (Fin 2)) x).source
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U
    (fun x ↦ (chartAt (EuclideanSpace ℝ (Fin 2)) x).open_source) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, mem_chart_source _ x⟩)
  have hchoose : ∀ x : S, ∃ i : S, i ∈ t ∧ x ∈ U i := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hit, hx⟩ := Set.mem_iUnion.mp hi
    exact ⟨i, hit, hx⟩
  let idx : S → S := fun x ↦ (hchoose x).choose
  have hidx_mem (x : S) : idx x ∈ t := (hchoose x).choose_spec.1
  have hxsource (x : S) : x ∈ U (idx x) := (hchoose x).choose_spec.2
  let f : S → (Shrink.{0} ↥t × EuclideanSpace ℝ (Fin 2)) := fun x ↦
    ((equivShrink.{0} ↥t) ⟨idx x, hidx_mem x⟩,
      chartAt (EuclideanSpace ℝ (Fin 2)) (idx x) x)
  apply small_of_injective (f := f)
  intro x y hxy
  have hidx_sub : (⟨idx x, hidx_mem x⟩ : ↥t) = ⟨idx y, hidx_mem y⟩ := by
    apply (equivShrink.{0} ↥t).injective
    exact congr_arg Prod.fst hxy
  have hidx : idx x = idx y := congr_arg Subtype.val hidx_sub
  have hchart : chartAt (EuclideanSpace ℝ (Fin 2)) (idx x) x =
      chartAt (EuclideanSpace ℝ (Fin 2)) (idx x) y := by
    have := congr_arg Prod.snd hxy
    simpa [f, hidx] using this
  exact (chartAt (EuclideanSpace ℝ (Fin 2)) (idx x)).injOn
    (hxsource x) (hidx ▸ hxsource y) hchart

theorem t96A01_finiteIndexSubgroup_connectedCover
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (s : S)
    (n : ℕ) (hn : 0 < n) (H : Subgroup (FundamentalGroup S s))
    [H.FiniteIndex] (hindex : H.index = n) :
    ∃ (E : Type) (_ : TopologicalSpace E) (p : E → S) (e : E),
      IsCoveringMap p ∧ PathConnectedSpace E ∧ p e = s ∧
      Nat.card (p ⁻¹' {s}) = n ∧
      Nonempty (FundamentalGroup E e ≃* H) := by
  letI : LocPathConnectedSpace S :=
    ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 2)) S
  letI : PathConnectedSpace S := PathConnectedSpace.of_locPathConnectedSpace
  haveI : Small.{0} S := t96A01_surface_small S
  obtain ⟨E, topE, p, e, hp, hE, hpe, hcard, hpi⟩ :=
    connectedCover (t96A01_surface_semilocallySimplyConnected S) s H
  exact ⟨E, topE, p, e, hp, hE, hpe, hcard.trans hindex, hpi⟩

/-- **LIBRARY (finite-cover Euler characteristic and surface recognition).**
A connected `n`-sheeted cover of a genus-four surface has genus `3*n+1`.
The conclusion includes the harmless basepoint transport needed downstream. -/
theorem t96A01_connectedFiniteCover_surfaceFundamentalGroup
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (hgenus : Nonempty (S ≃ₜ Surface true 4)) (s : S)
    (n : ℕ) (hn : 0 < n)
    (E : Type*) [TopologicalSpace E] [PathConnectedSpace E]
    (p : E → S) (e : E) (hp : IsCoveringMap p) (hpe : p e = s)
    (hsheets : Nat.card (p ⁻¹' {s}) = n) :
    Nonempty
      (FundamentalGroup E e ≃*
        FundamentalGroup (Surface true (3 * n + 1))
          (T96A01SurfaceBase (3 * n + 1))) := by
  sorry

theorem apm_t96a01
    {S : Type*} [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    [T2Space S] [SecondCountableTopology S] [CompactSpace S] [ConnectedSpace S]
    (hgenus : Nonempty (S ≃ₜ Surface true 4)) (s : S)
    (n : ℕ) (H : Subgroup (FundamentalGroup S s))
    [H.FiniteIndex] (hindex : H.index = n) :
    Nonempty (H ≃* OrientableSurfaceGroup (3 * n + 1)) := by
  have hn : 0 < n := t96A01_index_pos H n hindex
  obtain ⟨E, topE, p, e, hp, hE, hpe, hsheets, hsubgroup⟩ :=
    t96A01_finiteIndexSubgroup_connectedCover s n hn H hindex
  letI : TopologicalSpace E := topE
  letI : PathConnectedSpace E := hE
  obtain ⟨hsurface⟩ :=
    t96A01_connectedFiniteCover_surfaceFundamentalGroup
      hgenus s n hn E p e hp hpe hsheets
  obtain ⟨hsubgroup⟩ := hsubgroup
  obtain ⟨hpi₁⟩ := t96A01_orientableSurface_fundamentalGroup (3 * n + 1)
  exact ⟨hsubgroup.symm.trans (hsurface.trans hpi₁)⟩

#print axioms apm_t96a01
