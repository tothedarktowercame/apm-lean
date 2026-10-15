import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.AttachTwoCell
import ConstructionTargets.GenusTwoSurfacePiOne
import ConstructionTargets.PolygonSurfaceHomology

/-!
# π₁ of one-vertex polygon surfaces via a single 2-cell

Banked from the closed t97A01 blueprint (claude-14 + lemma seats, 2026-10-15).
For any one-vertex `PairingData P`:

* `polygonCellHomeomorph P : P.Space ≃ₜ Cell (polygonBoundaryWedgeLoop P)`:
  the polygon quotient is the wedge of orbit circles with one 2-cell attached
  along the boundary word;
* `legEquiv P : FreeGroup (PairingOrbit P.pair) ≃* π₁(wedge, base)`: the wedge
  π₁ is free on its legs (`finiteWedgeFinLegFreeGroupMap_injective`);
* `polygon_piOne_presentation`: a relator normally generating the boundary
  word's class presents `π₁(P.Space, P.center)`.
-/

open CategoryTheory Set

noncomputable section

namespace ConstructionTargets.PolygonCellPiOne

open ConstructionTargets
open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfacePiOne.PointWedgeQuotient
open ConstructionTargets.AttachTwoCell

/-! ### Group theory -/

/-- Pulling a one-relator kernel back along an isomorphism. -/
theorem ker_comp_mulEquiv_normalClosure {F G H : Type*} [Group F] [Group G]
    [Group H] (L : F ≃* G) (ψ : G →* H) (g : G) (r : F)
    (hψ : ψ.ker = Subgroup.normalClosure {g})
    (hr : Subgroup.normalClosure ({L r} : Set G) =
      Subgroup.normalClosure {g}) :
    (ψ.comp L.toMonoidHom).ker = Subgroup.normalClosure {r} := by
  have hmap : Subgroup.map L.toMonoidHom
      (Subgroup.normalClosure ({r} : Set F)) =
        Subgroup.normalClosure ({L r} : Set G) := by
    rw [Subgroup.map_normalClosure _ _ L.surjective, Set.image_singleton]
    rfl
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hψ, ← hr,
    ← hmap]
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have : y = x := L.injective hyx
    rwa [← this]
  · intro hx
    exact Subgroup.mem_map_of_mem _ hx

/-- Post-composing with an isomorphism does not change the kernel. -/
theorem ker_mulEquiv_comp {G H K : Type*} [Group G] [Group H] [Group K]
    (ψ : G →* H) (i : H ≃* K) :
    (i.toMonoidHom.comp ψ).ker = ψ.ker := by
  ext x
  simp [MonoidHom.mem_ker]

/-! ### Generic part: any one-vertex `PairingData` -/

section Generic

variable (P : PairingData)

/-- The ordered polygon boundary word, as a loop in the orbit wedge. -/
noncomputable abbrev bword :
    C(Circle, FiniteWedge (PairingOrbit P.pair)) :=
  PolygonSurfaceHomology.polygonBoundaryWedgeLoop P

/-- The wedge base point. -/
noncomputable abbrev wBase : FiniteWedge (PairingOrbit P.pair) :=
  PolygonSurfaceHomology.orbitWedgeBase P

instance orbit_nonempty : Nonempty (PairingOrbit P.pair) :=
  ⟨P.orbit ⟨0, P.edgeCount_pos⟩⟩

/-- The characteristic map of the cell
respects the polygon identifications.  Route: induct on `EqvGen`; for a
generator `edgePoint n i t ~ edgePoint n (P.pair i) (pairedParameter ..)`
rewrite both points as `circleToDisk (edgePointCircle P.edgeCount _ _)`
(`Subtype.ext` + `simp [circleToDisk, PolygonSurfaceHomology.circleToPolygonDisk,
edgePointCircle, Surfaces.edgePoint]`), use the cell boundary relation
`cellDisk γ (circleToDisk z) = cellIncl γ (γ z)` (`Quotient.sound` of
`CellRel.boundary z`, symm), then
`PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint` twice and
`(P.signedWedgeArc_pair i t).symm`.  This is `X_fwd_aux_edges` of
`problems/t97J04/lean/Main.lean` with `8` replaced by `P.edgeCount`. -/
lemma polyToCell_respects_aux_boundary {Y : Type} [TopologicalSpace Y]
    (γ : C(Circle, Y)) (z : Circle) :
    cellDisk γ (circleToDisk z) = cellIncl γ (γ z) := by
  exact Quotient.sound (Relation.EqvGen.symm _ _
    (Relation.EqvGen.rel _ _ (CellRel.boundary z)))

lemma polyToCell_respects_aux_edge (i : Fin P.edgeCount)
    (t : Set.Icc (0 : ℝ) 1) :
    cellDisk (bword P) (Surfaces.edgePoint P.edgeCount i t) =
      cellDisk (bword P) (Surfaces.edgePoint P.edgeCount (P.pair i)
        (pairedParameter P.pair P.sign i t)) := by
  rw [show Surfaces.edgePoint P.edgeCount i t =
      circleToDisk (edgePointCircle P.edgeCount i t) by
        rfl,
    show Surfaces.edgePoint P.edgeCount (P.pair i)
        (pairedParameter P.pair P.sign i t) =
      circleToDisk (edgePointCircle P.edgeCount (P.pair i)
        (pairedParameter P.pair P.sign i t)) by
        rfl,
    polyToCell_respects_aux_boundary, polyToCell_respects_aux_boundary]
  congr 1
  rw [PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint,
    PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint]
  exact (P.signedWedgeArc_pair i t).symm

lemma polyToCell_respects (x y : Surfaces.Disk)
    (h : Relation.EqvGen P.Rel x y) :
    cellDisk (bword P) x = cellDisk (bword P) y := by
  induction h with
  | rel x y h =>
      rcases h with ⟨i, t, rfl, rfl⟩
      exact polyToCell_respects_aux_edge P i t
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- Polygon quotient → cell: the disk is the 2-cell. -/
noncomputable def polyToCell : P.Space → Cell (bword P) :=
  Quotient.lift (fun z => cellDisk (bword P) z)
    (fun a b h => polyToCell_respects P a b h)

theorem continuous_polyToCell : Continuous (polyToCell P) := by
  apply continuous_coinduced_dom.mpr
  exact (cellDisk (bword P)).continuous

/-- Wedge → polygon quotient, through the banked skeleton homeomorphism. -/
noncomputable def wedgeToPoly (w : FiniteWedge (PairingOrbit P.pair)) :
    P.Space :=
  (P.skeletonHomeomorphWedge.symm w).1

theorem wedgeToPoly_bword (z : Circle) :
    wedgeToPoly P (bword P z) = P.quotientMap (circleToDisk z) := by
  change (P.skeletonHomeomorphWedge.symm (P.skeletonHomeomorphWedge
    (PolygonSurfaceHomology.polygonBoundarySkeletonLoop P z))).1 = _
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- Cell → polygon quotient. -/
noncomputable def cellToPoly : Cell (bword P) → P.Space :=
  Quotient.lift (Sum.elim (wedgeToPoly P) P.quotientMap) (by
    intro a b h
    change Relation.EqvGen (CellRel (bword P)) a b at h
    induction h with
    | rel a b h =>
        cases h with
        | boundary z => exact wedgeToPoly_bword P z
    | refl a => rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

theorem continuous_cellToPoly : Continuous (cellToPoly P) := by
  apply continuous_coinduced_dom.mpr
  apply continuous_sum_dom.mpr
  exact ⟨continuous_subtype_val.comp P.skeletonHomeomorphWedge.symm.continuous,
    P.continuous_quotientMap⟩

theorem cellToPoly_polyToCell (x : P.Space) :
    cellToPoly P (polyToCell P x) = x := by
  induction x using Quotient.inductionOn with
  | h z => rfl

/-- Every point of the cell lies on the
2-cell.  Route: `inr z` is `cellDisk _ z`; for `inl w` first show
`bword P` is surjective (copy `Xc_points_aux_word_surjective` of
`problems/t97J04/lean/Main.lean`, which is already stated for its `P` but
uses only `polygonBoundaryWedgeLoop_edgePoint`, `signedWedgeArc_of_sign`,
`signedWedgeArc_of_not_sign`, `reverseIcc_reverseIcc`,
`surjective_circleArc`), then `cellIncl γ (γ u) = cellDisk γ (circleToDisk u)`
(`Quotient.sound` of `CellRel.boundary u`). -/
lemma cellDisk_surjective_aux_bword : Function.Surjective (bword P) := by
  intro w
  induction w using Quotient.inductionOn with
  | h q =>
      rcases q with ⟨o, z⟩
      induction o using Quotient.inductionOn with
      | h i =>
          obtain ⟨t, ht⟩ := surjective_circleArc z
          by_cases hs : P.sign i
          · refine ⟨edgePointCircle P.edgeCount i t, ?_⟩
            change PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
                (edgePointCircle P.edgeCount i t) =
              PointWedgeQuotient.wedgeCircle (P.orbit i) z
            rw [PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint,
              P.signedWedgeArc_of_sign i t hs, ht]
          · refine ⟨edgePointCircle P.edgeCount i (reverseIcc t), ?_⟩
            have hs0 : P.sign i = false := Bool.eq_false_of_not_eq_true hs
            change PolygonSurfaceHomology.polygonBoundaryWedgeLoop P
                (edgePointCircle P.edgeCount i (reverseIcc t)) =
              PointWedgeQuotient.wedgeCircle (P.orbit i) z
            rw [PolygonSurfaceHomology.polygonBoundaryWedgeLoop_edgePoint,
              P.signedWedgeArc_of_not_sign i _ hs0,
              reverseIcc_reverseIcc, ht]

lemma cellDisk_surjective : Function.Surjective (cellDisk (bword P)) := by
  intro p
  induction p using Quotient.inductionOn with
  | h q =>
      rcases q with w | z
      · obtain ⟨u, rfl⟩ := cellDisk_surjective_aux_bword P w
        refine ⟨circleToDisk u, ?_⟩
        exact (Quotient.sound
          (Relation.EqvGen.rel _ _ (CellRel.boundary (γ := bword P) u))).symm
      · exact ⟨z, rfl⟩

theorem polyToCell_cellToPoly (p : Cell (bword P)) :
    polyToCell P (cellToPoly P p) = p := by
  obtain ⟨z, rfl⟩ := cellDisk_surjective P p
  rfl

/-- **Generic library result.**  A one-vertex polygon quotient is the orbit
wedge of circles with one 2-cell attached along the boundary word. -/
noncomputable def polygonCellHomeomorph : P.Space ≃ₜ Cell (bword P) where
  toFun := polyToCell P
  invFun := cellToPoly P
  left_inv := cellToPoly_polyToCell P
  right_inv := polyToCell_cellToPoly P
  continuous_toFun := continuous_polyToCell P
  continuous_invFun := continuous_cellToPoly P

end Generic

/-- The canonical positive-leg map
`FreeGroup (Fin (n+1)) → π₁(FiniteWedge (Fin (n+1)), wedgeCircle 0 1)` is
injective.  Route: `e := Classical.choose (finiteWedge_finSucc_fundamentalGroup_free n)`
with `FiniteWedgeFreeCoordinates n e`:
`e (apm_t92J05_finiteWedgeLegMap n i apm_t92J05_circlePositiveClass) = of i`.
`finiteWedgeFinLegMap n i` and `apm_t92J05_finiteWedgeLegMap n i` are the same
`FundamentalGroup.mapOfEq` (check `rfl`).  `circlePositiveFundamentalClass`
is a generator of `π₁(S¹,1) ≅ ℤ` (`CircleUniversalCover.circleFundamentalGroupMulEquivInt`),
so it equals `apm_t92J05_circlePositiveClass ^ s` with `s = ±1`
(compare `apm_t92J05_..._wedge_hcoord_aux_circle` in `GenusTwoSurfacePiOne`
and `circleIntegerLoopOneCoordinate_eq_one_or_neg_one`).  Hence
`e ∘ finiteWedgeFinLegFreeGroupMap n = FreeGroup.lift (fun i => of i ^ s)`,
an involutive endomorphism of the free group, hence injective. -/
lemma finiteWedgeFinLegFreeGroupMap_injective_aux_legMap (n : ℕ)
    (i : Fin (n + 1)) :
    PolygonSurfaceHomology.finiteWedgeFinLegMap n i =
      apm_t92J05_finiteWedgeLegMap n i := by
  rfl

lemma finiteWedgeFinLegFreeGroupMap_injective_aux_oldPositive :
    apm_t92J05_circlePositiveClass =
      PolygonSurfaceHomology.circleIntegerLoopOneClass := by
  apply ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt.injective
  simp [apm_t92J05_circlePositiveClass,
    PolygonSurfaceHomology.circleIntegerLoopOneClass,
    ConstructionTargets.CircleUniversalCover.circleFundamentalGroupMulEquivInt,
    ConstructionTargets.CircleUniversalCover.circleWindingHom_mk]

lemma finiteWedgeFinLegFreeGroupMap_injective (n : ℕ) :
    Function.Injective (PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap n) := by
  let e := Classical.choose (finiteWedge_finSucc_fundamentalGroup_free n)
  have he := Classical.choose_spec (finiteWedge_finSucc_fundamentalGroup_free n)
  let s := PolygonSurfaceHomology.circleIntegerLoopOneCoordinate
  have hleg (i : Fin (n + 1)) :
      e (PolygonSurfaceHomology.finiteWedgeFinLegMap n i
          PolygonSurfaceHomology.circlePositiveFundamentalClass) =
        FreeGroup.of i ^ s := by
    rw [PolygonSurfaceHomology.circlePositiveFundamentalClass_eq_integerLoop_zpow_coordinate,
      map_zpow, finiteWedgeFinLegFreeGroupMap_injective_aux_legMap,
      ← finiteWedgeFinLegFreeGroupMap_injective_aux_oldPositive]
    rw [map_zpow]
    exact congrArg (fun z => z ^ s) (he i)
  let d : FreeGroup (Fin (n + 1)) →* FreeGroup (Fin (n + 1)) :=
    FreeGroup.lift (fun i => FreeGroup.of i ^ s)
  have hcomp :
      e.toMonoidHom.comp
          (PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap n) = d := by
    apply FreeGroup.ext_hom
    intro i
    simpa [d, PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap] using hleg i
  have hs := PolygonSurfaceHomology.circleIntegerLoopOneCoordinate_eq_one_or_neg_one
  change s = 1 ∨ s = -1 at hs
  intro x y hxy
  have hd : d x = d y := by
    rw [← hcomp]
    exact congrArg e hxy
  rcases hs with hs | hs
  · have did : d = MonoidHom.id (FreeGroup (Fin (n + 1))) := by
      apply FreeGroup.ext_hom
      intro i
      simp [d, hs]
    simpa [did] using hd
  · have dinv (z : FreeGroup (Fin (n + 1))) : d (d z) = z := by
      induction z using FreeGroup.induction_on with
      | C1 => simp [d]
      | of i => simp [d, hs]
      | inv_of i hi => simp [d, hs]
      | mul a b ha hb => simp only [map_mul, ha, hb]
    simpa [dinv x, dinv y] using congrArg d hd

theorem finiteWedgeFinLegFreeGroupMapCard_injective (N : ℕ) (hN : 0 < N) :
    Function.Injective
      (PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMapCard N hN) := by
  cases N with
  | zero => omega
  | succ n =>
      simpa [PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMapCard,
        PolygonSurfaceHomology.finiteWedgeFinLegMapCard,
        PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap,
        PolygonSurfaceHomology.finiteWedgeFinLegMap] using
        finiteWedgeFinLegFreeGroupMap_injective n

section Generic2

variable (P : PairingData)

theorem finiteWedgeLegFreeGroupMap_injective :
    Function.Injective (PolygonSurfaceHomology.finiteWedgeLegFreeGroupMap P) := by
  intro x y hxy
  have h := congrArg
    (PolygonSurfaceHomology.finiteWedgeOrbitFundamentalGroupEquivFinExplicit P) hxy
  rw [PolygonSurfaceHomology.finiteWedgeOrbitFreeGroupMapComparison,
    PolygonSurfaceHomology.finiteWedgeOrbitFreeGroupMapComparison] at h
  exact FreeGroup.map_injective
    (PolygonSurfaceHomology.pairingOrbitEquivFinZero P).injective
    (finiteWedgeFinLegFreeGroupMapCard_injective _ _ h)

/-- `π₁` of the orbit wedge is free on the orbit legs. -/
noncomputable def legEquiv :
    FreeGroup (PairingOrbit P.pair) ≃*
      FundamentalGroup (FiniteWedge (PairingOrbit P.pair)) (wBase P) :=
  MulEquiv.ofBijective (PolygonSurfaceHomology.finiteWedgeLegFreeGroupMap P)
    ⟨finiteWedgeLegFreeGroupMap_injective P,
      PolygonSurfaceHomology.finiteWedgeLegFreeGroupMap_surjective P⟩

/-- The boundary word's based loop class in the wedge. -/
noncomputable abbrev wordClass :
    FundamentalGroup (FiniteWedge (PairingOrbit P.pair)) (wBase P) :=
  loopClassAt (bword P) (wBase P)
    (PolygonSurfaceHomology.polygonBoundaryWedgeLoop_one P)

/-- Van Kampen for the attached cell (sorry-free from `AttachTwoCell`). -/
theorem cell_bword_piOne :
    Function.Surjective
        (FundamentalGroup.map (cellIncl (bword P)) (wBase P)) ∧
      (FundamentalGroup.map (cellIncl (bword P)) (wBase P)).ker =
        Subgroup.normalClosure {wordClass P} := by
  obtain ⟨hA1, hA2, hA3, hA4, hA5⟩ := cell_facts (bword P)
  exact cell_piOne (bword P) (wBase P)
    (PolygonSurfaceHomology.polygonBoundaryWedgeLoop_one P) hA1 hA2 hA3 hA4 hA5
    (cell_pathConnected (bword P) hA3 hA4) cell_piOne_aux_hequiv_bijective
    cell_piOne_aux_homotopic_conj (cell_piOne_aux_overlap_generator (bword P) hA3)

instance cell_pathConnectedSpace : PathConnectedSpace (Cell (bword P)) :=
  cell_pc (bword P)

instance space_pathConnectedSpace : PathConnectedSpace P.Space :=
  (polygonCellHomeomorph P).symm.surjective.pathConnectedSpace
    (polygonCellHomeomorph P).symm.continuous

/-- Base-point and homeomorphism transport from the cell to the polygon
centre. -/
noncomputable def cellToCenterEquiv :
    FundamentalGroup (Cell (bword P)) (cellIncl (bword P) (wBase P)) ≃*
      FundamentalGroup P.Space P.center :=
  (PolygonSurfaceHomology.fundamentalGroupEquivOfHomeomorphEq (polygonCellHomeomorph P).symm
      (cellIncl (bword P) (wBase P)) _ rfl).trans
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected _ P.center)

/-- **Generic library result.**  For any one-vertex polygon quotient and any
group `F` identified with the free group on the edge orbits, a single
relator `r` whose image normally generates the same subgroup as the boundary
word presents `π₁(P.Space, centre)`. -/
theorem polygon_piOne_presentation {F : Type*} [Group F]
    (M : F ≃* FreeGroup (PairingOrbit P.pair)) (r : F)
    (hr : Subgroup.normalClosure ({legEquiv P (M r)} :
        Set (FundamentalGroup (FiniteWedge (PairingOrbit P.pair)) (wBase P))) =
      Subgroup.normalClosure {wordClass P}) :
    Nonempty (FundamentalGroup P.Space P.center ≃*
      F ⧸ Subgroup.normalClosure ({r} : Set F)) := by
  obtain ⟨hsurj, hker⟩ := cell_bword_piOne P
  let L : F ≃* FundamentalGroup (FiniteWedge (PairingOrbit P.pair)) (wBase P) :=
    M.trans (legEquiv P)
  let ψ := FundamentalGroup.map (cellIncl (bword P)) (wBase P)
  let Φ : F →* FundamentalGroup P.Space P.center :=
    (cellToCenterEquiv P).toMonoidHom.comp (ψ.comp L.toMonoidHom)
  have hΦs : Function.Surjective Φ :=
    (cellToCenterEquiv P).surjective.comp (hsurj.comp L.surjective)
  have hΦk : Φ.ker = Subgroup.normalClosure {r} := by
    rw [ker_mulEquiv_comp]
    exact ker_comp_mulEquiv_normalClosure L ψ (wordClass P) r hker hr
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective Φ hΦs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hΦk)⟩

end Generic2

end ConstructionTargets.PolygonCellPiOne
