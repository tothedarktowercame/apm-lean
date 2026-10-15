import Mathlib
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import ConstructionTargets.Surfaces
import ConstructionTargets.t97A01Closure
import ConstructionTargets.AttachTwoCell

/-!
# APM t97A01 — the nonorientable genus-three surface

## Statement repairs

None.

## Encoding note

Both requested surfaces are actual polygon quotients of the closed unit disk.
The first glues the six boundary edges with word `a a b b c c`; the second
uses `a b a⁻¹ b⁻¹ c c`, the torus connected-summed with `ℝP²`. The conclusion
uses singular homology of these spaces and the fundamental group of the
second quotient, rather than detached cellular arithmetic.
-/

open CategoryTheory Set

noncomputable section

abbrev apm_t97a01_Disk := Metric.closedBall (0 : ℂ) 1

/-- The point at parameter `t` on edge `j` of a regular hexagonal boundary
parameterization of the disk. -/
def apm_t97a01_edgePoint (j : Fin 6) (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_Disk :=
  ⟨Complex.exp (Complex.I * (2 * Real.pi * ((j : ℝ) + t.1) / 6)), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    simp⟩

/-- Edge identifications for the word `a a b b c c`. -/
inductive apm_t97a01_RelX : apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 0 t) (apm_t97a01_edgePoint 1 t)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 2 t) (apm_t97a01_edgePoint 3 t)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelX (apm_t97a01_edgePoint 4 t) (apm_t97a01_edgePoint 5 t)

/-- Edge identifications for the word `a b a⁻¹ b⁻¹ c c`. -/
inductive apm_t97a01_RelTorusRP2 :
    apm_t97a01_Disk → apm_t97a01_Disk → Prop
  | a (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 0 t)
        (apm_t97a01_edgePoint 2 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | b (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 1 t)
        (apm_t97a01_edgePoint 3 ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩)
  | c (t : Set.Icc (0 : ℝ) 1) :
      apm_t97a01_RelTorusRP2 (apm_t97a01_edgePoint 4 t)
        (apm_t97a01_edgePoint 5 t)

def apm_t97a01_X := Quotient (Relation.EqvGen.setoid apm_t97a01_RelX)
def apm_t97a01_TorusRP2 :=
  Quotient (Relation.EqvGen.setoid apm_t97a01_RelTorusRP2)

noncomputable instance : TopologicalSpace apm_t97a01_X :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

noncomputable instance : TopologicalSpace apm_t97a01_TorusRP2 :=
  TopologicalSpace.coinduced (fun x : apm_t97a01_Disk ↦ Quotient.mk _ x) inferInstance

def apm_t97a01_quotientX : apm_t97a01_Disk → apm_t97a01_X :=
  fun x => Quotient.mk _ x

def apm_t97a01_quotientTorusRP2 : apm_t97a01_Disk → apm_t97a01_TorusRP2 :=
  fun x => Quotient.mk _ x

lemma apm_t97a01_continuous_quotientX : Continuous apm_t97a01_quotientX := by
  exact continuous_coinduced_rng

lemma apm_t97a01_surjective_quotientX :
    Function.Surjective apm_t97a01_quotientX := by
  exact Quotient.mk_surjective

lemma apm_t97a01_continuous_quotientTorusRP2 :
    Continuous apm_t97a01_quotientTorusRP2 := by
  exact continuous_coinduced_rng

lemma apm_t97a01_surjective_quotientTorusRP2 :
    Function.Surjective apm_t97a01_quotientTorusRP2 := by
  exact Quotient.mk_surjective

lemma apm_t97a01_quotientX_identifies_a (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_quotientX (apm_t97a01_edgePoint 0 t) =
      apm_t97a01_quotientX (apm_t97a01_edgePoint 1 t) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (.a t))

lemma apm_t97a01_quotientTorusRP2_identifies_c (t : Set.Icc (0 : ℝ) 1) :
    apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 4 t) =
      apm_t97a01_quotientTorusRP2 (apm_t97a01_edgePoint 5 t) := by
  exact Quotient.sound (Relation.EqvGen.rel _ _ (.c t))

/-- Every generating identification for `X` is a generating identification
in the repository's canonical nonorientable genus-three polygon. -/
lemma apm_t97a01_RelX_to_standardN3 {x y : apm_t97a01_Disk}
    (h : apm_t97a01_RelX x y) :
    ConstructionTargets.Surfaces.SurfaceRel false 3 x y := by
  cases h with
  | a t =>
      refine ⟨0, by omega, t, ?_, ?_⟩
      · rfl
      · rfl
  | b t =>
      refine ⟨1, by omega, t, ?_, ?_⟩
      · rfl
      · rfl
  | c t =>
      refine ⟨2, by omega, t, ?_, ?_⟩
      · rfl
      · rfl

/-- Conversely, the canonical genus-three relation has exactly the three
generators used in `apm_t97a01_RelX`. -/
lemma apm_t97a01_standardN3_to_RelX {x y : apm_t97a01_Disk}
    (h : ConstructionTargets.Surfaces.SurfaceRel false 3 x y) :
    apm_t97a01_RelX x y := by
  rcases h with ⟨j, hj, t, rfl, rfl⟩
  interval_cases j
  · exact .a t
  · exact .b t
  · exact .c t

/-- The `aa bb cc` quotient is definitionally equivalent to the reusable
canonical polygon presentation of the nonorientable genus-three surface. -/
def apm_t97a01_X_equiv_standardN3 :
    apm_t97a01_X ≃ ConstructionTargets.Surfaces.Surface false 3 := by
  apply Quotient.congrRight
  intro x y
  have hrel : apm_t97a01_RelX =
      ConstructionTargets.Surfaces.SurfaceRel false 3 := by
    funext u v
    apply propext
    exact ⟨apm_t97a01_RelX_to_standardN3, apm_t97a01_standardN3_to_RelX⟩
  rw [hrel]

/-- The quotient equivalence with the canonical nonorientable genus-three
surface respects the coinduced topologies on both polygon quotients. -/
def apm_t97a01_X_homeomorph_standardN3 :
    apm_t97a01_X ≃ₜ ConstructionTargets.Surfaces.Surface false 3 where
  toEquiv := apm_t97a01_X_equiv_standardN3
  continuous_toFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : apm_t97a01_Disk =>
      apm_t97a01_X_equiv_standardN3 (Quotient.mk _ x))
    simpa [apm_t97a01_X_equiv_standardN3] using
      (ConstructionTargets.Surfaces.continuous_surfaceQuotient false 3)
  continuous_invFun := by
    apply isQuotientMap_quotient_mk'.continuous_iff.mpr
    change Continuous (fun x : ConstructionTargets.Surfaces.Disk =>
      apm_t97a01_X_equiv_standardN3.symm (Quotient.mk _ x))
    simpa [apm_t97a01_X_equiv_standardN3] using apm_t97a01_continuous_quotientX

/-- The first frozen quotient is the exact pairing-space input to the banked
polygon homology theorem. -/
def apm_t97a01_X_homeomorph_pairingSpace :
    apm_t97a01_X ≃ₜ
      ConstructionTargets.t97A01Closure.aabbccPairingData.Space :=
  apm_t97a01_X_homeomorph_standardN3.trans
    (ConstructionTargets.PolygonSurfacePiOne.standardPairingData_space_homeomorph
      false 3 (by omega)).symm

/-- The frozen torus-crosscap generators are the canonical literal
torus-crosscap generators used by the polygon library. -/
lemma apm_t97a01_RelTorusRP2_to_canonical {x y : apm_t97a01_Disk}
    (h : apm_t97a01_RelTorusRP2 x y) :
    ConstructionTargets.PolygonTorusCrosscapRelation.TorusCrosscapRel x y := by
  cases h with
  | a t => exact .a t
  | b t => exact .b t
  | c t => exact .c t

/-- Conversely, every canonical literal torus-crosscap generator is one of
the frozen generators. -/
lemma apm_t97a01_canonical_to_RelTorusRP2 {x y : apm_t97a01_Disk}
    (h : ConstructionTargets.PolygonTorusCrosscapRelation.TorusCrosscapRel x y) :
    apm_t97a01_RelTorusRP2 x y := by
  cases h with
  | a t => exact .a t
  | b t => exact .b t
  | c t => exact .c t

theorem apm_t97a01_torusRP2_eqvGen_iff (x y : apm_t97a01_Disk) :
    Relation.EqvGen apm_t97a01_RelTorusRP2 x y ↔
      Relation.EqvGen
        ConstructionTargets.PolygonTorusCrosscapRelation.TorusCrosscapRel x y := by
  constructor
  · intro h
    induction h with
    | rel x y h => exact .rel _ _ (apm_t97a01_RelTorusRP2_to_canonical h)
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂
  · intro h
    induction h with
    | rel x y h => exact .rel _ _ (apm_t97a01_canonical_to_RelTorusRP2 h)
    | refl x => exact .refl x
    | symm x y _ ih => exact .symm x y ih
    | trans x y z _ _ ih₁ ih₂ => exact .trans x y z ih₁ ih₂

/-- The second frozen quotient is the exact pairing-space input to the
banked polygon homology theorem. -/
def apm_t97a01_TorusRP2_homeomorph_pairingSpace :
    apm_t97a01_TorusRP2 ≃ₜ
      ConstructionTargets.t97A01Closure.torusRP2PairingData.Space :=
  ConstructionTargets.t97A01Closure.quotientHomeomorphOfEqvGenIff
    apm_t97a01_RelTorusRP2
    ConstructionTargets.t97A01Closure.torusRP2PairingData.Rel
    isQuotientMap_quotient_mk' isQuotientMap_quotient_mk'
    (fun x y => (apm_t97a01_torusRP2_eqvGen_iff x y).trans
      (ConstructionTargets.PolygonSurfacePiOne.torusRP2_eqvGen_iff x y).symm)

abbrev apm_t97a01_H (k : ℕ) (Y : Type) [TopologicalSpace Y] :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).obj (TopCat.of Y))

/-- Homology transport from the frozen `aabbcc` quotient to the pairing-space
model used by the polygon Mayer--Vietoris calculation. -/
noncomputable def apm_t97a01_X_homologyIsoPairingSpace (k : ℕ) :
    apm_t97a01_H k apm_t97a01_X ≅
      ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.aabbccPairingData k :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo apm_t97a01_X_homeomorph_pairingSpace)

/-- Homology transport from the frozen torus-crosscap quotient to the
pairing-space model used by the polygon Mayer--Vietoris calculation. -/
noncomputable def apm_t97a01_TorusRP2_homologyIsoPairingSpace (k : ℕ) :
    apm_t97a01_H k apm_t97a01_TorusRP2 ≅
      ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.torusRP2PairingData k :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℤ) k).obj
    (ModuleCat.of ℤ ℤ)).mapIso
      (TopCat.isoOfHomeo apm_t97a01_TorusRP2_homeomorph_pairingSpace)

theorem apm_t97a01_aabbcc_homology_isZero (k : ℕ) (hk : 2 ≤ k) :
    Limits.IsZero
      (ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.aabbccPairingData k) := by
  rcases ConstructionTargets.t97A01Closure.aabbccPolygonHomology with
    ⟨_, _, ⟨h2⟩, hhi⟩
  rcases eq_or_lt_of_le hk with rfl | hk'
  · have hz : Limits.IsZero
        (ModuleCat.of ℤ
          (ConstructionTargets.PolygonSurfaceHomology.BoundaryKernel
            ConstructionTargets.t97A01Closure.aabbccPairingData)) := by
      rw [ConstructionTargets.t97A01Closure.aabbccBoundaryKernel_eq_bot]
      exact ModuleCat.isZero_of_subsingleton _
    exact hz.of_iso h2
  · exact hhi k (by omega)

theorem apm_t97a01_torusRP2_homology_isZero (k : ℕ) (hk : 2 ≤ k) :
    Limits.IsZero
      (ConstructionTargets.PolygonSurfaceHomology.H
        ConstructionTargets.t97A01Closure.torusRP2PairingData k) := by
  rcases ConstructionTargets.t97A01Closure.torusRP2PolygonHomology with
    ⟨_, _, ⟨h2⟩, hhi⟩
  rcases eq_or_lt_of_le hk with rfl | hk'
  · have hz : Limits.IsZero
        (ModuleCat.of ℤ
          (ConstructionTargets.PolygonSurfaceHomology.BoundaryKernel
            ConstructionTargets.t97A01Closure.torusRP2PairingData)) := by
      rw [ConstructionTargets.t97A01Closure.torusRP2BoundaryKernel_eq_bot]
      exact ModuleCat.isZero_of_subsingleton _
    exact hz.of_iso h2
  · exact hhi k (by omega)

/-- The integral singular homology of both frozen six-edge quotients. -/
theorem apm_t97a01_polygon_singular_homology :
    (Nonempty (apm_t97a01_H 0 apm_t97a01_X ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t97a01_H 1 apm_t97a01_X ≅
        ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
      ∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_X)) ∧
    (Nonempty (apm_t97a01_H 0 apm_t97a01_TorusRP2 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (apm_t97a01_H 1 apm_t97a01_TorusRP2 ≅
        ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
      ∀ k : ℕ, 2 ≤ k → Limits.IsZero
        (apm_t97a01_H k apm_t97a01_TorusRP2)) := by
  rcases ConstructionTargets.t97A01Closure.aabbccPolygonHomology with
    ⟨⟨hX0⟩, ⟨hX1⟩, _, _⟩
  rcases ConstructionTargets.t97A01Closure.torusRP2PolygonHomology with
    ⟨⟨hT0⟩, ⟨hT1⟩, _, _⟩
  refine ⟨⟨⟨apm_t97a01_X_homologyIsoPairingSpace 0 ≪≫ hX0⟩,
    ⟨apm_t97a01_X_homologyIsoPairingSpace 1 ≪≫ hX1 ≪≫
      ConstructionTargets.t97A01Closure.aabbccBoundaryCokernelSmithEquiv.toModuleIso⟩,
    ?_⟩,
    ⟨⟨apm_t97a01_TorusRP2_homologyIsoPairingSpace 0 ≪≫ hT0⟩,
    ⟨apm_t97a01_TorusRP2_homologyIsoPairingSpace 1 ≪≫ hT1 ≪≫
      ConstructionTargets.t97A01Closure.torusRP2BoundaryCokernelSmithEquiv.toModuleIso⟩,
    ?_⟩⟩
  · intro k hk
    exact (apm_t97a01_aabbcc_homology_isZero k hk).of_iso
      (apm_t97a01_X_homologyIsoPairingSpace k)
  · intro k hk
    exact (apm_t97a01_torusRP2_homology_isZero k hk).of_iso
      (apm_t97a01_TorusRP2_homologyIsoPairingSpace k)

#print axioms apm_t97a01_polygon_singular_homology

def apm_t97a01_baseX : apm_t97a01_X := Quotient.mk _ (0 : apm_t97a01_Disk)
def apm_t97a01_baseTorusRP2 : apm_t97a01_TorusRP2 :=
  Quotient.mk _ (0 : apm_t97a01_Disk)

@[simp] theorem apm_t97a01_TorusRP2_homeomorph_pairingSpace_base :
    apm_t97a01_TorusRP2_homeomorph_pairingSpace apm_t97a01_baseTorusRP2 =
      ConstructionTargets.t97A01Closure.torusRP2PairingData.center := by
  rfl

/-- The frozen based fundamental group is exactly the pairing-space based
fundamental group to which the radial van Kampen computation applies. -/
noncomputable def apm_t97a01_TorusRP2_fundamentalGroupEquivPairingSpace :
    FundamentalGroup apm_t97a01_TorusRP2 apm_t97a01_baseTorusRP2 ≃*
      FundamentalGroup
        ConstructionTargets.t97A01Closure.torusRP2PairingData.Space
        ConstructionTargets.t97A01Closure.torusRP2PairingData.center := by
  rw [← apm_t97a01_TorusRP2_homeomorph_pairingSpace_base]
  exact ConstructionTargets.t97A01Closure.fundamentalGroupEquivOfHomeomorph
    apm_t97a01_TorusRP2_homeomorph_pairingSpace apm_t97a01_baseTorusRP2

#print axioms apm_t97a01_TorusRP2_fundamentalGroupEquivPairingSpace

def apm_t97a01_relator : FreeGroup (Fin 3) :=
  (.of 0) * (.of 1) * (.of 0)⁻¹ * (.of 1)⁻¹ * (.of 2) * (.of 2)


/-! ## Blueprint (2026-10-15): `π₁` of a one-vertex polygon quotient via `AttachTwoCell`

Route.  For any one-vertex `PairingData P`, the polygon quotient `P.Space`
is homeomorphic to `Cell (polygonBoundaryWedgeLoop P)` — the orbit wedge of
circles with one disk attached along the boundary word (generic
generalisation of `X_fwd`/`X_bwd`/`Xc_points` of `problems/t97J04`).
`AttachTwoCell.cell_piOne` then makes `π₁(wedge) → π₁(cell)` onto with kernel
the normal closure of the word's loop class, and `π₁(wedge)` is free on the
orbit legs (`finiteWedgeLegFreeGroupMap`, surjective banked, injectivity a
leaf).  For `T # ℝP²` the boundary word in leg coordinates is already banked
in `t97A01Closure.torusRP2AttachingWord` (skeleton coordinates); one leaf
transports it to the wedge. -/

namespace APMT97A01BP

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

/-- LEAF G1 (generic, ~40 lines).  The characteristic map of the cell
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
-- BEGIN SEAT AREA
lemma polyToCell_respects (x y : Surfaces.Disk)
    (h : Relation.EqvGen P.Rel x y) :
    cellDisk (bword P) x = cellDisk (bword P) y := by
  sorry
-- END SEAT AREA

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

/-- LEAF G2 (generic, ~45 lines).  Every point of the cell lies on the
2-cell.  Route: `inr z` is `cellDisk _ z`; for `inl w` first show
`bword P` is surjective (copy `Xc_points_aux_word_surjective` of
`problems/t97J04/lean/Main.lean`, which is already stated for its `P` but
uses only `polygonBoundaryWedgeLoop_edgePoint`, `signedWedgeArc_of_sign`,
`signedWedgeArc_of_not_sign`, `reverseIcc_reverseIcc`,
`surjective_circleArc`), then `cellIncl γ (γ u) = cellDisk γ (circleToDisk u)`
(`Quotient.sound` of `CellRel.boundary u`). -/
lemma cellDisk_surjective : Function.Surjective (cellDisk (bword P)) := by
  sorry

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

/-- LEAF G3 (generic, ~80–120 lines).  The canonical positive-leg map
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
lemma finiteWedgeFinLegFreeGroupMap_injective (n : ℕ) :
    Function.Injective (PolygonSurfaceHomology.finiteWedgeFinLegFreeGroupMap n) := by
  sorry

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
  (t97A01Closure.fundamentalGroupEquivOfHomeomorph (polygonCellHomeomorph P).symm
      (cellIncl (bword P) (wBase P))).trans
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

/-! ### The torus-crosscap specialisation -/

/-- Fin-3 generators ↦ orbit generators, in the basis that matches the
geometric boundary orientation (banked in `t97A01Closure`). -/
noncomputable def torusRP2GenEquiv :
    FreeGroup (Fin 3) ≃*
      FreeGroup (PairingOrbit t97A01Closure.torusRP2PairingData.pair) :=
  t97A01Closure.torusRP2BoundaryBasisEquiv.trans
    t97A01Closure.torusRP2OrbitFreeGroupEquiv.symm

/-- LEAF W (problem-specific, ~60 lines).  The frozen relator, in leg
coordinates, normally generates the boundary word's class in the wedge.
Route: `t97A01Closure.torusRP2AttachingWord` is exactly this statement in
skeleton coordinates.  Apply `Subgroup.map_normalClosure` with the
`MulEquiv` `t97A01Closure.torusRP2SkeletonFundamentalGroupEquivWedge`
(surjective) to both sides.  Left side: `torusRP2SkeletonFinFreeGroupMap =
EquivWedge.symm ∘ finiteWedgeLegFreeGroupMap ∘ torusRP2OrbitFreeGroupEquiv.symm`
by definition, `legEquiv P x = finiteWedgeLegFreeGroupMap P x`
(`MulEquiv.ofBijective_apply`), and `torusRP2BoundaryBasisEquiv` unfolds by
`by_cases circleIntegerLoopOneCoordinate = 1` to the same `if` branch as in
`torusRP2AttachingWord` (see the end of `torusRP2Relator_normalClosure_le_kernel`);
`apm_t97a01_relator = t97A01Closure.torusRP2FrozenRelator` is `rfl`.
Right side: `wordClass P = Path.Homotopic.Quotient.mk (polygonBoundaryIntegerLoopPath P)`
(unfold `loopClassAt`, `circleIntegerLoopOneClass`,
`polygonBoundaryIntegerLoopPath`; the cast lemmas are definitional — compare
the `simpa` in `word_loopClass_coords` of `problems/t97J04`). -/
lemma torusRP2_boundary_word :
    Subgroup.normalClosure ({legEquiv t97A01Closure.torusRP2PairingData
        (torusRP2GenEquiv apm_t97a01_relator)} :
        Set (FundamentalGroup
          (FiniteWedge (PairingOrbit t97A01Closure.torusRP2PairingData.pair))
          (wBase t97A01Closure.torusRP2PairingData))) =
      Subgroup.normalClosure {wordClass t97A01Closure.torusRP2PairingData} := by
  sorry

theorem torusRP2_pairingSpace_piOne :
    Nonempty (FundamentalGroup t97A01Closure.torusRP2PairingData.Space
        t97A01Closure.torusRP2PairingData.center ≃*
      PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))) :=
  polygon_piOne_presentation t97A01Closure.torusRP2PairingData torusRP2GenEquiv
    apm_t97a01_relator torusRP2_boundary_word

end APMT97A01BP


theorem apm_t97a01 :
    Nonempty (apm_t97a01_H 0 apm_t97a01_X ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_X ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_X)) ∧
    Nonempty (apm_t97a01_H 0 apm_t97a01_TorusRP2 ≅ ModuleCat.of ℤ ℤ) ∧
    Nonempty (apm_t97a01_H 1 apm_t97a01_TorusRP2 ≅
      ModuleCat.of ℤ (ℤ × ℤ × ZMod 2)) ∧
    (∀ k : ℕ, 2 ≤ k → Limits.IsZero (apm_t97a01_H k apm_t97a01_TorusRP2)) ∧
    Nonempty
      (FundamentalGroup apm_t97a01_TorusRP2 apm_t97a01_baseTorusRP2 ≃*
        PresentedGroup ({apm_t97a01_relator} : Set (FreeGroup (Fin 3)))) := by
  rcases apm_t97a01_polygon_singular_homology with
    ⟨⟨hX0, hX1, hXhi⟩, hT0, hT1, hThi⟩
  obtain ⟨e⟩ := APMT97A01BP.torusRP2_pairingSpace_piOne
  exact ⟨hX0, hX1, hXhi, hT0, hT1, hThi,
    ⟨apm_t97a01_TorusRP2_fundamentalGroupEquivPairingSpace.trans e⟩⟩

#print axioms apm_t97a01
