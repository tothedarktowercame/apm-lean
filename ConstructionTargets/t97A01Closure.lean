import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.T97A01SmithQuotients
import ConstructionTargets.t93J03Closure

/-!
# Closure adapters for t97A01

This module specializes the general polygon-surface homology theorem to the
two six-edge pairing records occurring in the frozen problem.  Later closure
steps identify these quotient spaces with the literal `EqvGen` quotients and
reduce the displayed kernel and cokernel models to the requested groups.
-/

open CategoryTheory CategoryTheory.Limits Topology

noncomputable section

namespace ConstructionTargets.t97A01Closure

open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfaceHomology
open ConstructionTargets.T97A01SmithQuotients
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.TwoOpenFundamentalGroupoidSpan
open ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
open ConstructionTargets.t93J03Closure

/-- A homeomorphism transports the based fundamental group. -/
def fundamentalGroupEquivOfHomeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) where
  toFun := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩
    (e.symm_apply_apply x)
  left_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.map_apply]
      change (FundamentalGroup.mapOfEq _ _)
        (Path.Homotopic.Quotient.mk (p.map e.continuous)) = _
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.symm_apply_apply (p t)
  right_inv p := by
    induction p using Path.Homotopic.Quotient.ind with
    | mk p =>
      rw [FundamentalGroup.mapOfEq_apply]
      apply Path.Homotopic.Quotient.eq.mpr
      convert Path.Homotopic.refl p using 1
      ext t
      exact e.apply_symm_apply (p t)
  map_mul' := map_mul _

/-- Two quotients of the same source by extensionally equal generated
relations are homeomorphic whenever their canonical projections carry the
quotient topologies.  This is the exact adapter used for the frozen literal
`EqvGen` quotient types. -/
def quotientHomeomorphOfEqvGenIff {X : Type*} [TopologicalSpace X]
    (R S : X → X → Prop)
    [TopologicalSpace (Quotient (Relation.EqvGen.setoid R))]
    [TopologicalSpace (Quotient (Relation.EqvGen.setoid S))]
    (hR : IsQuotientMap
      (Quotient.mk (Relation.EqvGen.setoid R) :
        X → Quotient (Relation.EqvGen.setoid R)))
    (hS : IsQuotientMap
      (Quotient.mk (Relation.EqvGen.setoid S) :
        X → Quotient (Relation.EqvGen.setoid S)))
    (hrel : ∀ x y, Relation.EqvGen R x y ↔ Relation.EqvGen S x y) :
    Quotient (Relation.EqvGen.setoid R) ≃ₜ
      Quotient (Relation.EqvGen.setoid S) where
  toEquiv := by
    apply Quotient.congrRight
    exact hrel
  continuous_toFun := hR.continuous_iff.mpr (by
    simpa using hS.continuous)
  continuous_invFun := hS.continuous_iff.mpr (by
    simpa using hR.continuous)

/-- Pairing data for the frozen `a a b b c c` polygon. -/
def aabbccPairingData : PairingData :=
  nonorientableStandardPairingData 3 (by omega)

/-- Pairing data for the frozen `a b a⁻¹ b⁻¹ c c` polygon. -/
def torusRP2PairingData : PairingData :=
  ConstructionTargets.PolygonSurfacePiOne.torusRP2PairingData

@[simp] theorem aabbccPairingData_edgeCount :
    aabbccPairingData.edgeCount = 6 := rfl

@[simp] theorem torusRP2PairingData_edgeCount :
    torusRP2PairingData.edgeCount = 6 := rfl

/-- The complete general polygon homology calculation, specialized to the
`aabbcc` presentation before its finite integer-linear reduction. -/
theorem aabbccPolygonHomology :
    Nonempty (H aabbccPairingData 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H aabbccPairingData 1 ≅
        ModuleCat.of ℤ (BoundaryCokernel aabbccPairingData)) ∧
      Nonempty (H aabbccPairingData 2 ≅
        ModuleCat.of ℤ (BoundaryKernel aabbccPairingData)) ∧
      ∀ k : ℕ, 3 ≤ k → IsZero (H aabbccPairingData k) :=
  polygonQuotient_homology aabbccPairingData

/-- The complete general polygon homology calculation, specialized to the
torus-crosscap presentation before its finite integer-linear reduction. -/
theorem torusRP2PolygonHomology :
    Nonempty (H torusRP2PairingData 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H torusRP2PairingData 1 ≅
        ModuleCat.of ℤ (BoundaryCokernel torusRP2PairingData)) ∧
      Nonempty (H torusRP2PairingData 2 ≅
        ModuleCat.of ℤ (BoundaryKernel torusRP2PairingData)) ∧
      ∀ k : ℕ, 3 ≤ k → IsZero (H torusRP2PairingData k) :=
  polygonQuotient_homology torusRP2PairingData

/-! ## Attaching maps in the three named edge coordinates -/

/-- Evaluation on the three named `aabbcc` edge orbits. -/
def aabbccOrbitCoordinates :
    (PairingOrbit aabbccPairingData.pair → ℤ) ≃ₗ[ℤ] Z3 :=
  { toFun := fun f => (f ((nonorientableOrbitEquiv 3).symm 0),
        f ((nonorientableOrbitEquiv 3).symm 1),
        f ((nonorientableOrbitEquiv 3).symm 2))
    invFun := fun v q => ![v.1, v.2.1, v.2.2] (nonorientableOrbitEquiv 3 q)
    left_inv := by
      intro f
      funext q
      generalize hj : nonorientableOrbitEquiv 3 q = j
      fin_cases j <;>
        simpa [hj] using congrArg f ((nonorientableOrbitEquiv 3).symm_apply_apply q)
    right_inv := by rintro ⟨x, y, z⟩; rfl
    map_add' := by intro f g; rfl
    map_smul' := by intro n f; rfl }

@[simp] theorem aabbcc_orbit_eq_named (i : Fin 6) (j : Fin 3) :
    aabbccPairingData.orbit i = (nonorientableOrbitEquiv 3).symm j ↔
      nonorientableOrbitEquiv 3 (aabbccPairingData.orbit i) = j :=
  (nonorientableOrbitEquiv 3).eq_symm_apply

@[simp] theorem torusRP2_orbit_eq_named (i : Fin 6) (j : Fin 3) :
    torusRP2PairingData.orbit i = torusRP2OrbitEquiv.symm j ↔
      torusRP2OrbitEquiv (torusRP2PairingData.orbit i) = j :=
  torusRP2OrbitEquiv.eq_symm_apply

@[simp] theorem aabbccOrbitEquiv_orbit (i : Fin 6) :
    nonorientableOrbitEquiv 3 (aabbccPairingData.orbit i) =
      nonorientableOrbitLabel 3 i := rfl

@[simp] theorem torusRP2OrbitEquiv_orbit (i : Fin 6) :
    torusRP2OrbitEquiv (torusRP2PairingData.orbit i) =
      torusRP2OrbitLabel i := rfl

/-- Evaluation on the named `a`, `b`, and `c` torus-crosscap edge orbits. -/
def torusRP2OrbitCoordinates :
    (PairingOrbit torusRP2PairingData.pair → ℤ) ≃ₗ[ℤ] Z3 :=
  { toFun := fun f => (f (torusRP2OrbitEquiv.symm 0),
        f (torusRP2OrbitEquiv.symm 1), f (torusRP2OrbitEquiv.symm 2))
    invFun := fun v q => ![v.1, v.2.1, v.2.2] (torusRP2OrbitEquiv q)
    left_inv := by
      intro f
      funext q
      generalize hj : torusRP2OrbitEquiv q = j
      fin_cases j <;>
        simpa [hj] using congrArg f (torusRP2OrbitEquiv.symm_apply_apply q)
    right_inv := by rintro ⟨x, y, z⟩; rfl
    map_add' := by intro f g; rfl
    map_smul' := by intro n f; rfl }

theorem aabbcc_attachingDegree_named (j : Fin 3) :
    attachingDegree aabbccPairingData ((nonorientableOrbitEquiv 3).symm j) = -2 := by
  rw [attachingDegree_apply]
  simp_rw [edgeOrbitContribution, aabbcc_orbit_eq_named]
  simp_rw [aabbccOrbitEquiv_orbit]
  fin_cases j <;>
    simp [aabbccPairingData, nonorientableStandardPairingData,
      standardPairingDataOfOneVertex, standardPair, standardSign,
      nonorientableOrbitLabel, nonorientableCoord, edgeAttachingDegree] <;>
      decide

theorem aabbccOrbitCoordinates_attachingDegree :
    aabbccOrbitCoordinates (attachingDegree aabbccPairingData) = (-2, -2, -2) := by
  apply Prod.ext
  · exact aabbcc_attachingDegree_named 0
  · apply Prod.ext
    · exact aabbcc_attachingDegree_named 1
    · exact aabbcc_attachingDegree_named 2

theorem torusRP2_attachingDegree_named (j : Fin 3) :
    attachingDegree torusRP2PairingData (torusRP2OrbitEquiv.symm j) = ![0, 0, -2] j := by
  rw [attachingDegree_apply]
  simp_rw [edgeOrbitContribution, torusRP2_orbit_eq_named]
  simp_rw [torusRP2OrbitEquiv_orbit]
  fin_cases j <;>
    simp [torusRP2PairingData, PolygonSurfacePiOne.torusRP2PairingData,
      torusRP2OrbitLabel, torusRP2Pair, torusRP2Sign, edgeAttachingDegree] <;>
      decide

theorem torusRP2OrbitCoordinates_attachingDegree :
    torusRP2OrbitCoordinates (attachingDegree torusRP2PairingData) = (0, 0, -2) := by
  apply Prod.ext
  · exact torusRP2_attachingDegree_named 0
  · apply Prod.ext
    · exact torusRP2_attachingDegree_named 1
    · exact torusRP2_attachingDegree_named 2

theorem aabbccOrbitCoordinates_comp_attachingBoundary :
    aabbccOrbitCoordinates.toLinearMap.comp (attachingBoundary aabbccPairingData) =
      -standardN3BoundaryLinear := by
  apply LinearMap.ext
  intro n
  change aabbccOrbitCoordinates (n • attachingDegree aabbccPairingData) = _
  rw [map_smul, aabbccOrbitCoordinates_attachingDegree]
  ext <;> simp [standardN3BoundaryLinear, mul_comm]

theorem torusRP2OrbitCoordinates_comp_attachingBoundary :
    torusRP2OrbitCoordinates.toLinearMap.comp (attachingBoundary torusRP2PairingData) =
      -torusCrosscapBoundaryLinear := by
  apply LinearMap.ext
  intro n
  change torusRP2OrbitCoordinates (n • attachingDegree torusRP2PairingData) = _
  rw [map_smul, torusRP2OrbitCoordinates_attachingDegree]
  ext <;> simp [torusCrosscapBoundaryLinear, mul_comm]

theorem aabbccAttachingBoundary_injective :
    Function.Injective (attachingBoundary aabbccPairingData) := by
  intro x y hxy
  apply standardN3BoundaryLinear_injective
  have hc := congrArg aabbccOrbitCoordinates hxy
  have heq := aabbccOrbitCoordinates_comp_attachingBoundary
  have hx := LinearMap.congr_fun heq x
  have hy := LinearMap.congr_fun heq y
  simpa [LinearMap.comp_apply] using hx.symm.trans (hc.trans hy)

theorem torusRP2AttachingBoundary_injective :
    Function.Injective (attachingBoundary torusRP2PairingData) := by
  intro x y hxy
  apply torusCrosscapBoundaryLinear_injective
  have hc := congrArg torusRP2OrbitCoordinates hxy
  have heq := torusRP2OrbitCoordinates_comp_attachingBoundary
  have hx := LinearMap.congr_fun heq x
  have hy := LinearMap.congr_fun heq y
  simpa [LinearMap.comp_apply] using hx.symm.trans (hc.trans hy)

theorem aabbccBoundaryKernel_eq_bot : BoundaryKernel aabbccPairingData = ⊥ :=
  LinearMap.ker_eq_bot.mpr aabbccAttachingBoundary_injective

theorem torusRP2BoundaryKernel_eq_bot : BoundaryKernel torusRP2PairingData = ⊥ :=
  LinearMap.ker_eq_bot.mpr torusRP2AttachingBoundary_injective

theorem aabbccOrbitCoordinates_map_boundaryRange :
    Submodule.map aabbccOrbitCoordinates.toLinearMap
        (LinearMap.range (attachingBoundary aabbccPairingData)) =
      LinearMap.range standardN3BoundaryLinear := by
  rw [← LinearMap.range_comp,
    aabbccOrbitCoordinates_comp_attachingBoundary, LinearMap.range_neg]

theorem torusRP2OrbitCoordinates_map_boundaryRange :
    Submodule.map torusRP2OrbitCoordinates.toLinearMap
        (LinearMap.range (attachingBoundary torusRP2PairingData)) =
      LinearMap.range torusCrosscapBoundaryLinear := by
  rw [← LinearMap.range_comp,
    torusRP2OrbitCoordinates_comp_attachingBoundary, LinearMap.range_neg]

/-- A linear equivalence descends to quotient modules when it carries the
source submodule exactly onto the target submodule. -/
noncomputable def quotientLinearEquivOfMapEq
    {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N]
    (e : M ≃ₗ[ℤ] N) (p : Submodule ℤ M) (q : Submodule ℤ N)
    (h : Submodule.map e.toLinearMap p = q) :
    (M ⧸ p) ≃ₗ[ℤ] (N ⧸ q) := by
  let f : (M ⧸ p) →ₗ[ℤ] (N ⧸ q) :=
    p.mapQ q e.toLinearMap (by
      intro x hx
      change e x ∈ q
      rw [← h]
      exact ⟨x, hx, rfl⟩)
  let g : (N ⧸ q) →ₗ[ℤ] (M ⧸ p) :=
    q.mapQ p e.symm.toLinearMap (by
      intro y hy
      change e.symm y ∈ p
      have hy' : y ∈ Submodule.map e.toLinearMap p := h.symm ▸ hy
      rcases hy' with ⟨x, hx, hxy⟩
      simpa [← hxy] using hx)
  exact LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro x
      refine Quotient.inductionOn x ?_
      intro x
      change (Quotient.mk _ (e (e.symm x))) = Quotient.mk _ x
      rw [e.apply_symm_apply])
    (by
      apply LinearMap.ext
      intro y
      refine Quotient.inductionOn y ?_
      intro y
      change (Quotient.mk _ (e.symm (e y))) = Quotient.mk _ y
      rw [e.symm_apply_apply])

noncomputable def aabbccBoundaryCokernelCoordinateEquiv :
    BoundaryCokernel aabbccPairingData ≃ₗ[ℤ]
      (Z3 ⧸ LinearMap.range standardN3BoundaryLinear) :=
  quotientLinearEquivOfMapEq aabbccOrbitCoordinates _ _
    aabbccOrbitCoordinates_map_boundaryRange

noncomputable def torusRP2BoundaryCokernelCoordinateEquiv :
    BoundaryCokernel torusRP2PairingData ≃ₗ[ℤ]
      (Z3 ⧸ LinearMap.range torusCrosscapBoundaryLinear) :=
  quotientLinearEquivOfMapEq torusRP2OrbitCoordinates _ _
    torusRP2OrbitCoordinates_map_boundaryRange

noncomputable def standardN3RangeQuotientSmithEquiv :
    (Z3 ⧸ LinearMap.range standardN3BoundaryLinear) ≃ₗ[ℤ] Smith :=
  (Submodule.quotEquivOfEq _ _ standardN3_range_eq_ker) ≪≫ₗ
    standardN3Coordinate.quotKerEquivOfSurjective standardN3Coordinate_surjective

noncomputable def torusCrosscapRangeQuotientSmithEquiv :
    (Z3 ⧸ LinearMap.range torusCrosscapBoundaryLinear) ≃ₗ[ℤ] Smith :=
  (Submodule.quotEquivOfEq _ _ torusCrosscap_range_eq_ker) ≪≫ₗ
    torusCrosscapCoordinate.quotKerEquivOfSurjective
      torusCrosscapCoordinate_surjective

noncomputable def aabbccBoundaryCokernelSmithEquiv :
    BoundaryCokernel aabbccPairingData ≃ₗ[ℤ] Smith :=
  aabbccBoundaryCokernelCoordinateEquiv ≪≫ₗ standardN3RangeQuotientSmithEquiv

noncomputable def torusRP2BoundaryCokernelSmithEquiv :
    BoundaryCokernel torusRP2PairingData ≃ₗ[ℤ] Smith :=
  torusRP2BoundaryCokernelCoordinateEquiv ≪≫ₗ
    torusCrosscapRangeQuotientSmithEquiv

/-! ### Fundamental-group coordinates for the torus-crosscap skeleton -/

/-- The point of the polygon skeleton lying over the distinguished common
point of the orbit-indexed circle wedge. -/
noncomputable def torusRP2SkeletonBase : torusRP2PairingData.skeleton :=
  torusRP2PairingData.skeletonHomeomorphWedge.symm
    (orbitWedgeBase torusRP2PairingData)

@[simp] theorem torusRP2SkeletonHomeomorphWedge_base :
    torusRP2PairingData.skeletonHomeomorphWedge torusRP2SkeletonBase =
      orbitWedgeBase torusRP2PairingData := by
  exact torusRP2PairingData.skeletonHomeomorphWedge.apply_symm_apply _

@[simp] theorem torusRP2SkeletonHomeomorphWedge_symm_base :
    torusRP2PairingData.skeletonHomeomorphWedge.symm
        (orbitWedgeBase torusRP2PairingData) = torusRP2SkeletonBase := rfl

/-- Based fundamental groups of the literal polygon skeleton and its
orbit-indexed circle wedge agree. -/
noncomputable def torusRP2SkeletonFundamentalGroupEquivWedge :
    FundamentalGroup torusRP2PairingData.skeleton torusRP2SkeletonBase ≃*
      FundamentalGroup
        (PointWedgeQuotient.FiniteWedge
          (PairingOrbit torusRP2PairingData.pair))
        (orbitWedgeBase torusRP2PairingData) :=
  ConstructionTargets.PolygonSurfaceHomology.fundamentalGroupEquivOfHomeomorphEq
    torusRP2PairingData.skeletonHomeomorphWedge torusRP2SkeletonBase
    (orbitWedgeBase torusRP2PairingData)
    torusRP2SkeletonHomeomorphWedge_base

/-- The signed orbit generators give a canonical epimorphism from their free
group onto the based fundamental group of the torus-crosscap skeleton. -/
noncomputable def torusRP2SkeletonFreeGroupMap :
    FreeGroup (PairingOrbit torusRP2PairingData.pair) →*
      FundamentalGroup torusRP2PairingData.skeleton torusRP2SkeletonBase :=
  torusRP2SkeletonFundamentalGroupEquivWedge.symm.toMonoidHom.comp
    (finiteWedgeLegFreeGroupMap torusRP2PairingData)

theorem torusRP2SkeletonFreeGroupMap_surjective :
    Function.Surjective torusRP2SkeletonFreeGroupMap := by
  exact torusRP2SkeletonFundamentalGroupEquivWedge.symm.surjective.comp
    (finiteWedgeLegFreeGroupMap_surjective torusRP2PairingData)

/-- Relabel the three signed edge orbits by the frozen generator order. -/
noncomputable def torusRP2OrbitFreeGroupEquiv :
    FreeGroup (PairingOrbit torusRP2PairingData.pair) ≃* FreeGroup (Fin 3) :=
  MulEquiv.ofBijective (FreeGroup.map torusRP2OrbitEquiv)
    ⟨FreeGroup.map_injective torusRP2OrbitEquiv.injective,
      FreeGroup.map_surjective torusRP2OrbitEquiv.surjective⟩

/-- The exact `Fin 3`-ordered generator map onto the polygon skeleton. -/
noncomputable def torusRP2SkeletonFinFreeGroupMap :
    FreeGroup (Fin 3) →*
      FundamentalGroup torusRP2PairingData.skeleton torusRP2SkeletonBase :=
  torusRP2SkeletonFreeGroupMap.comp
    torusRP2OrbitFreeGroupEquiv.symm.toMonoidHom

theorem torusRP2SkeletonFinFreeGroupMap_surjective :
    Function.Surjective torusRP2SkeletonFinFreeGroupMap := by
  exact torusRP2SkeletonFreeGroupMap_surjective.comp
    torusRP2OrbitFreeGroupEquiv.symm.surjective

/-- Change from the signed polygon orientation to the frozen presentation:
the third generator is reversed, while the first two are fixed. -/
def torusRP2GeneratorSignHom : FreeGroup (Fin 3) →* FreeGroup (Fin 3) :=
  FreeGroup.lift fun i => if i = 2 then (FreeGroup.of i)⁻¹ else FreeGroup.of i

theorem torusRP2GeneratorSignHom_involutive :
    Function.Involutive torusRP2GeneratorSignHom := by
  intro x
  induction x using FreeGroup.induction_on with
  | C1 => simp
  | of i =>
      fin_cases i <;> simp [torusRP2GeneratorSignHom]
  | inv_of i h => simpa using congrArg Inv.inv h
  | mul x y hx hy => simp [hx, hy]

/-- The generator-sign change is an automorphism, not a change of the
presented group. -/
def torusRP2GeneratorSignEquiv : FreeGroup (Fin 3) ≃* FreeGroup (Fin 3) :=
  MulEquiv.ofBijective torusRP2GeneratorSignHom
    ⟨torusRP2GeneratorSignHom_involutive.injective,
      torusRP2GeneratorSignHom_involutive.surjective⟩

/-- Skeleton generators in the convention of the frozen relator. -/
noncomputable def torusRP2FrozenSkeletonFreeGroupMap :
    FreeGroup (Fin 3) →*
      FundamentalGroup torusRP2PairingData.skeleton torusRP2SkeletonBase :=
  torusRP2SkeletonFinFreeGroupMap.comp torusRP2GeneratorSignEquiv.toMonoidHom

theorem torusRP2FrozenSkeletonFreeGroupMap_surjective :
    Function.Surjective torusRP2FrozenSkeletonFreeGroupMap := by
  exact torusRP2SkeletonFinFreeGroupMap_surjective.comp
    torusRP2GeneratorSignEquiv.surjective

/-- The literal relator requested by the frozen theorem. -/
def torusRP2FrozenRelator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ *
    (FreeGroup.of 1)⁻¹ * FreeGroup.of 2 * FreeGroup.of 2

/-- The same boundary word in the signed polygon coordinates. -/
def torusRP2SignedRelator : FreeGroup (Fin 3) :=
  FreeGroup.of 0 * FreeGroup.of 1 * (FreeGroup.of 0)⁻¹ *
    (FreeGroup.of 1)⁻¹ * (FreeGroup.of 2)⁻¹ * (FreeGroup.of 2)⁻¹

theorem torusRP2GeneratorSignHom_frozenRelator :
    torusRP2GeneratorSignHom torusRP2FrozenRelator =
      torusRP2SignedRelator := by
  simp [torusRP2GeneratorSignHom, torusRP2FrozenRelator,
    torusRP2SignedRelator]

/-- Direct evaluation of the six oriented polygon edges in the signed
`Fin 3` coordinates. -/
theorem torusRP2PolygonBoundaryLegWord_coordinates :
    (polygonBoundaryLegWord torusRP2PairingData).map
        (fun q => (torusRP2OrbitEquiv q.1, q.2)) =
      [((0 : Fin 3), 1), ((1 : Fin 3), 1), ((0 : Fin 3), -1),
        ((1 : Fin 3), -1), ((2 : Fin 3), -1), ((2 : Fin 3), -1)] := by
  rfl

/-- The actual geometric boundary class is the ordered signed-edge product.
The reversal records Mathlib's `End` multiplication convention. -/
theorem polygonBoundaryIntegerLoopClass_eq_reverseExplicitEdgeProduct
    (P : PairingData) :
    (Path.Homotopic.Quotient.mk (polygonBoundaryIntegerLoopPath P) :
        FundamentalGroup _ _) =
      ((List.ofFn fun i : Fin P.edgeCount =>
        polygonBoundaryExplicitEdgeClass P i).reverse.prod) := by
  calc
    _ = Path.Homotopic.Quotient.mk
        (Path.concat (fun _ : Fin (P.edgeCount + 1) => orbitWedgeBase P)
          (polygonBoundaryCanonicalSubdivisionPathAtBase P)) :=
      Path.Homotopic.Quotient.eq.mpr
        (polygonBoundaryCanonicalConcat_homotopic P).symm
    _ = ((List.ofFn fun i : Fin P.edgeCount =>
          Path.Homotopic.Quotient.mk
            (polygonBoundaryCanonicalSubdivisionPathAtBase P i)) :
            List (FundamentalGroup _ _)).reverse.prod :=
      fundamentalGroup_mk_concat_eq_reverse_list_prod _ _ _
    _ = _ := by
      have hf :
          (fun i : Fin P.edgeCount =>
            (Path.Homotopic.Quotient.mk
              (polygonBoundaryCanonicalSubdivisionPathAtBase P i) :
                FundamentalGroup _ _)) =
            fun i => polygonBoundaryExplicitEdgeClass P i := by
        funext i
        rw [polygonBoundaryCanonicalSubdivisionPathAtBase_eq,
          polygonBoundarySubdivisionPathAtBase_eq_signedEdge]
        exact polygonBoundarySignedEdgePathAtBase_mk P i
      rw [hf]
      rfl

/-- Specialization of the exact path-level boundary product to the
torus-crosscap polygon. -/
theorem torusRP2GeometricBoundary_eq_signedEdgeProduct :
    (Path.Homotopic.Quotient.mk
        (polygonBoundaryIntegerLoopPath torusRP2PairingData) :
      FundamentalGroup _ _) =
      ((List.ofFn fun i : Fin torusRP2PairingData.edgeCount =>
        polygonBoundaryExplicitEdgeClass torusRP2PairingData i).reverse.prod) :=
  polygonBoundaryIntegerLoopClass_eq_reverseExplicitEdgeProduct _

/-- Transport to the common wedge basepoint preserves the global circle
orientation formula. -/
theorem finiteWedgeExplicitLegClassAtBase_eq_positive_zpow
    (P : PairingData) (l : PairingOrbit P.pair) :
    finiteWedgeExplicitLegClassAtBase P l =
      finiteWedgeLegFundamentalClassAtBase P l ^
        circleIntegerLoopOneCoordinate := by
  rcases circleIntegerLoopOneCoordinate_eq_one_or_neg_one with h | h
  · rw [h, zpow_one, finiteWedgeExplicitLegClassAtBase,
      finiteWedgeExplicitLegClass_eq_positive_zpow, h, zpow_one]
    rfl
  · rw [h, zpow_neg_one, finiteWedgeExplicitLegClassAtBase,
      finiteWedgeExplicitLegClass_eq_positive_zpow, h, zpow_neg_one]
    exact homotopicQuotient_cast_symm _ _

/-- Every geometric edge factor is the corresponding normalized generator,
with the edge sign multiplied by the single global circle-orientation unit. -/
theorem polygonBoundaryExplicitEdgeClass_eq_zpow (P : PairingData)
    (i : Fin P.edgeCount) :
    polygonBoundaryExplicitEdgeClass P i =
      finiteWedgeLegFundamentalClassAtBase P (P.orbit i) ^
        ((if P.sign i then (1 : ℤ) else -1) *
          circleIntegerLoopOneCoordinate) := by
  cases hs : P.sign i
  · simp [polygonBoundaryExplicitEdgeClass, hs,
      finiteWedgeExplicitLegClassAtBase_eq_positive_zpow, zpow_neg]
  · simp [polygonBoundaryExplicitEdgeClass, hs,
      finiteWedgeExplicitLegClassAtBase_eq_positive_zpow]

/-- The three normalized wedge generators in the signed orbit order. -/
noncomputable def torusRP2WedgeGenerator (j : Fin 3) :=
  finiteWedgeLegFundamentalClassAtBase torusRP2PairingData
    (torusRP2OrbitEquiv.symm j)

theorem torusRP2_orbit_eq_label (i : Fin 6) :
    torusRP2PairingData.orbit i =
      torusRP2OrbitEquiv.symm (torusRP2OrbitLabel i) := by
  apply torusRP2OrbitEquiv.injective
  rw [torusRP2OrbitEquiv_orbit, torusRP2OrbitEquiv.apply_symm_apply]

@[simp] theorem torusRP2PairingData_sign (i : Fin 6) :
    torusRP2PairingData.sign i = torusRP2Sign i := rfl

/-- Evaluation of the reversed six-edge product forced by the fundamental
group multiplication convention. -/
theorem torusRP2SignedEdgeProduct_explicit :
    ((List.ofFn fun i : Fin torusRP2PairingData.edgeCount =>
      polygonBoundaryExplicitEdgeClass torusRP2PairingData i).reverse.prod) =
      torusRP2WedgeGenerator 2 ^ (-circleIntegerLoopOneCoordinate) *
      (torusRP2WedgeGenerator 2 ^ (-circleIntegerLoopOneCoordinate) *
      (torusRP2WedgeGenerator 1 ^ (-circleIntegerLoopOneCoordinate) *
      (torusRP2WedgeGenerator 0 ^ (-circleIntegerLoopOneCoordinate) *
      (torusRP2WedgeGenerator 1 ^ circleIntegerLoopOneCoordinate *
      (torusRP2WedgeGenerator 0 ^ circleIntegerLoopOneCoordinate * 1))))) := by
  simp [polygonBoundaryExplicitEdgeClass_eq_zpow,
    torusRP2PairingData_edgeCount, torusRP2Sign,
    torusRP2PairingData_sign,
    torusRP2WedgeGenerator, torusRP2_orbit_eq_label,
    torusRP2OrbitLabel]
  rfl

/-- Basis change matching the geometric boundary when the circle orientation
unit is `+1`. -/
def torusRP2PositiveBoundaryBasisHom :
    FreeGroup (Fin 3) →* FreeGroup (Fin 3) :=
  FreeGroup.lift fun i => ![(FreeGroup.of 1)⁻¹,
    (FreeGroup.of 0)⁻¹, (FreeGroup.of 2)⁻¹] i

theorem torusRP2PositiveBoundaryBasisHom_involutive :
    Function.Involutive torusRP2PositiveBoundaryBasisHom := by
  intro x
  induction x using FreeGroup.induction_on with
  | C1 => simp
  | of i => fin_cases i <;> simp [torusRP2PositiveBoundaryBasisHom]
  | inv_of i h => simpa using congrArg Inv.inv h
  | mul x y hx hy => simp [hx, hy]

def torusRP2PositiveBoundaryBasisEquiv :
    FreeGroup (Fin 3) ≃* FreeGroup (Fin 3) :=
  MulEquiv.ofBijective torusRP2PositiveBoundaryBasisHom
    ⟨torusRP2PositiveBoundaryBasisHom_involutive.injective,
      torusRP2PositiveBoundaryBasisHom_involutive.surjective⟩

/-- Basis change matching the geometric boundary when the circle orientation
unit is `-1`. -/
def torusRP2NegativeBoundaryBasisHom :
    FreeGroup (Fin 3) →* FreeGroup (Fin 3) :=
  FreeGroup.lift fun i => ![FreeGroup.of 1, FreeGroup.of 0, FreeGroup.of 2] i

theorem torusRP2NegativeBoundaryBasisHom_involutive :
    Function.Involutive torusRP2NegativeBoundaryBasisHom := by
  intro x
  induction x using FreeGroup.induction_on with
  | C1 => simp
  | of i => fin_cases i <;> simp [torusRP2NegativeBoundaryBasisHom]
  | inv_of i h => simpa using congrArg Inv.inv h
  | mul x y hx hy => simp [hx, hy]

def torusRP2NegativeBoundaryBasisEquiv :
    FreeGroup (Fin 3) ≃* FreeGroup (Fin 3) :=
  MulEquiv.ofBijective torusRP2NegativeBoundaryBasisHom
    ⟨torusRP2NegativeBoundaryBasisHom_involutive.injective,
      torusRP2NegativeBoundaryBasisHom_involutive.surjective⟩

theorem torusRP2PositiveBoundaryBasisHom_relator :
    (FreeGroup.of 2)⁻¹ * (FreeGroup.of 2)⁻¹ *
      torusRP2PositiveBoundaryBasisHom torusRP2FrozenRelator *
      (FreeGroup.of 2 * FreeGroup.of 2) =
      (FreeGroup.of 2)⁻¹ * (FreeGroup.of 2)⁻¹ *
        (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ *
          FreeGroup.of 1 * FreeGroup.of 0 := by
  simp [torusRP2PositiveBoundaryBasisHom, torusRP2FrozenRelator]
  group

theorem torusRP2NegativeBoundaryBasisHom_relator :
    FreeGroup.of 2 * FreeGroup.of 2 *
      torusRP2NegativeBoundaryBasisHom torusRP2FrozenRelator *
      (FreeGroup.of 2 * FreeGroup.of 2)⁻¹ =
      FreeGroup.of 2 * FreeGroup.of 2 * FreeGroup.of 1 * FreeGroup.of 0 *
        (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ := by
  simp [torusRP2NegativeBoundaryBasisHom, torusRP2FrozenRelator]
  group

/-- Conjugating a single relator does not change the normal subgroup it
normally generates. -/
theorem normalClosure_singleton_conj {G : Type*} [Group G] (g x : G) :
    Subgroup.normalClosure ({g * x * g⁻¹} : Set G) =
      Subgroup.normalClosure ({x} : Set G) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact Subgroup.normalClosure_normal.conj_mem x
      (Subgroup.subset_normalClosure (Set.mem_singleton x)) g
  · apply Subgroup.normalClosure_le_normal
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h := Subgroup.normalClosure_normal.conj_mem (g * x * g⁻¹)
      (Subgroup.subset_normalClosure (Set.mem_singleton (g * x * g⁻¹))) g⁻¹
    have heq : g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x := by group
    rw [heq] at h
    exact h

theorem torusRP2PositiveBoundary_normalClosure :
    Subgroup.normalClosure ({
      (FreeGroup.of 2)⁻¹ * (FreeGroup.of 2)⁻¹ *
        (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ *
          FreeGroup.of 1 * FreeGroup.of 0} : Set (FreeGroup (Fin 3))) =
      Subgroup.normalClosure ({
        torusRP2PositiveBoundaryBasisHom torusRP2FrozenRelator} :
          Set (FreeGroup (Fin 3))) := by
  rw [← torusRP2PositiveBoundaryBasisHom_relator]
  exact normalClosure_singleton_conj
    ((FreeGroup.of 2)⁻¹ * (FreeGroup.of 2)⁻¹)
    (torusRP2PositiveBoundaryBasisHom torusRP2FrozenRelator)

theorem torusRP2NegativeBoundary_normalClosure :
    Subgroup.normalClosure ({
      FreeGroup.of 2 * FreeGroup.of 2 * FreeGroup.of 1 * FreeGroup.of 0 *
        (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹} : Set (FreeGroup (Fin 3))) =
      Subgroup.normalClosure ({
        torusRP2NegativeBoundaryBasisHom torusRP2FrozenRelator} :
          Set (FreeGroup (Fin 3))) := by
  rw [← torusRP2NegativeBoundaryBasisHom_relator]
  exact normalClosure_singleton_conj
    (FreeGroup.of 2 * FreeGroup.of 2)
    (torusRP2NegativeBoundaryBasisHom torusRP2FrozenRelator)

/-- The skeleton epimorphism sends each finite-coordinate generator to the
corresponding normalized wedge loop, transported back across the skeleton
homeomorphism. -/
theorem torusRP2SkeletonFinFreeGroupMap_of (j : Fin 3) :
    torusRP2SkeletonFinFreeGroupMap (FreeGroup.of j) =
      torusRP2SkeletonFundamentalGroupEquivWedge.symm
        (torusRP2WedgeGenerator j) := by
  have hinv :
      torusRP2OrbitFreeGroupEquiv.symm (FreeGroup.of j) =
        FreeGroup.of (torusRP2OrbitEquiv.symm j) := by
    rw [torusRP2OrbitFreeGroupEquiv.symm_apply_eq]
    change FreeGroup.of j =
      FreeGroup.map torusRP2OrbitEquiv
        (FreeGroup.of (torusRP2OrbitEquiv.symm j))
    rw [FreeGroup.map.of, torusRP2OrbitEquiv.apply_symm_apply]
  rw [show torusRP2SkeletonFinFreeGroupMap (FreeGroup.of j) =
      torusRP2SkeletonFreeGroupMap
        (torusRP2OrbitFreeGroupEquiv.symm (FreeGroup.of j)) by rfl, hinv]
  change torusRP2SkeletonFundamentalGroupEquivWedge.symm
      ((FreeGroup.lift (finiteWedgeLegFundamentalClassAtBase torusRP2PairingData))
        (FreeGroup.of (torusRP2OrbitEquiv.symm j))) = _
  rw [FreeGroup.lift_apply_of]
  rfl

/-- In the positive circle orientation, the explicit free-group boundary
word maps to the literal geometric boundary loop in the polygon skeleton. -/
theorem torusRP2SkeletonFinFreeGroupMap_positiveBoundary
    (h : circleIntegerLoopOneCoordinate = 1) :
    torusRP2SkeletonFinFreeGroupMap
        ((FreeGroup.of 2)⁻¹ * (FreeGroup.of 2)⁻¹ *
          (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹ *
            FreeGroup.of 1 * FreeGroup.of 0) =
      torusRP2SkeletonFundamentalGroupEquivWedge.symm
        (Path.Homotopic.Quotient.mk
          (polygonBoundaryIntegerLoopPath torusRP2PairingData)) := by
  apply torusRP2SkeletonFundamentalGroupEquivWedge.injective
  rw [torusRP2SkeletonFundamentalGroupEquivWedge.apply_symm_apply]
  simp only [zpow_one, zpow_neg_one, map_mul, map_inv,
    torusRP2SkeletonFinFreeGroupMap_of, map_one,
    torusRP2SkeletonFundamentalGroupEquivWedge.apply_symm_apply]
  symm
  calc
    _ = ((List.ofFn fun i : Fin torusRP2PairingData.edgeCount =>
          polygonBoundaryExplicitEdgeClass torusRP2PairingData i).reverse.prod) :=
      torusRP2GeometricBoundary_eq_signedEdgeProduct
    _ = _ := by
      rw [torusRP2SignedEdgeProduct_explicit, h]
      simp only [zpow_one, zpow_neg_one, mul_one]
      group

/-- The analogous exact boundary transport in the negative circle
orientation. -/
theorem torusRP2SkeletonFinFreeGroupMap_negativeBoundary
    (h : circleIntegerLoopOneCoordinate = -1) :
    torusRP2SkeletonFinFreeGroupMap
        (FreeGroup.of 2 * FreeGroup.of 2 * FreeGroup.of 1 * FreeGroup.of 0 *
          (FreeGroup.of 1)⁻¹ * (FreeGroup.of 0)⁻¹) =
      torusRP2SkeletonFundamentalGroupEquivWedge.symm
        (Path.Homotopic.Quotient.mk
          (polygonBoundaryIntegerLoopPath torusRP2PairingData)) := by
  apply torusRP2SkeletonFundamentalGroupEquivWedge.injective
  rw [torusRP2SkeletonFundamentalGroupEquivWedge.apply_symm_apply]
  simp only [neg_neg, zpow_one, zpow_neg_one, map_mul, map_inv,
    torusRP2SkeletonFinFreeGroupMap_of, map_one,
    torusRP2SkeletonFundamentalGroupEquivWedge.apply_symm_apply]
  symm
  calc
    _ = ((List.ofFn fun i : Fin torusRP2PairingData.edgeCount =>
          polygonBoundaryExplicitEdgeClass torusRP2PairingData i).reverse.prod) :=
      torusRP2GeometricBoundary_eq_signedEdgeProduct
    _ = _ := by
      rw [torusRP2SignedEdgeProduct_explicit, h]
      simp only [neg_neg, zpow_one, zpow_neg_one, mul_one]
      group

/-- After transport to the skeleton, either orientation convention normally
generates the literal geometric attaching loop. -/
theorem torusRP2AttachingWord :
    Subgroup.normalClosure ({
      torusRP2SkeletonFinFreeGroupMap
        ((if circleIntegerLoopOneCoordinate = 1 then
            torusRP2PositiveBoundaryBasisHom
          else torusRP2NegativeBoundaryBasisHom) torusRP2FrozenRelator)} :
        Set (FundamentalGroup torusRP2PairingData.skeleton
          torusRP2SkeletonBase)) =
      Subgroup.normalClosure ({
        torusRP2SkeletonFundamentalGroupEquivWedge.symm
          (Path.Homotopic.Quotient.mk
            (polygonBoundaryIntegerLoopPath torusRP2PairingData))} :
        Set (FundamentalGroup torusRP2PairingData.skeleton
          torusRP2SkeletonBase)) := by
  rcases circleIntegerLoopOneCoordinate_eq_one_or_neg_one with h | h
  · rw [if_pos h]
    have hm := congrArg
      (fun H : Subgroup (FreeGroup (Fin 3)) =>
        H.map torusRP2SkeletonFinFreeGroupMap)
      torusRP2PositiveBoundary_normalClosure
    dsimp only at hm
    rw [Subgroup.map_normalClosure _ _
          torusRP2SkeletonFinFreeGroupMap_surjective,
        Subgroup.map_normalClosure _ _
          torusRP2SkeletonFinFreeGroupMap_surjective] at hm
    simp only [Set.image_singleton] at hm
    rw [← torusRP2SkeletonFinFreeGroupMap_positiveBoundary h]
    exact hm.symm
  · rw [if_neg (by omega : circleIntegerLoopOneCoordinate ≠ 1)]
    have hm := congrArg
      (fun H : Subgroup (FreeGroup (Fin 3)) =>
        H.map torusRP2SkeletonFinFreeGroupMap)
      torusRP2NegativeBoundary_normalClosure
    dsimp only at hm
    rw [Subgroup.map_normalClosure _ _
          torusRP2SkeletonFinFreeGroupMap_surjective,
        Subgroup.map_normalClosure _ _
          torusRP2SkeletonFinFreeGroupMap_surjective] at hm
    simp only [Set.image_singleton] at hm
    rw [← torusRP2SkeletonFinFreeGroupMap_negativeBoundary h]
    exact hm.symm

/-! ### The exact based van Kampen interface -/

/-- Literal inclusion of the boundary skeleton into the polygon quotient. -/
noncomputable def torusRP2SkeletonToPairingSpace :
    C(torusRP2PairingData.skeleton, torusRP2PairingData.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The based fundamental-group map induced by the literal skeleton
inclusion. -/
noncomputable def torusRP2SkeletonToPairingSpacePiOne :
    FundamentalGroup torusRP2PairingData.skeleton torusRP2SkeletonBase →*
      FundamentalGroup torusRP2PairingData.Space
        (torusRP2SkeletonToPairingSpace torusRP2SkeletonBase) :=
  FundamentalGroup.map torusRP2SkeletonToPairingSpace torusRP2SkeletonBase

/-- The once-around boundary loop before passing to the polygon quotient,
regarded as a based loop in the closed polygon disk. -/
noncomputable def torusRP2DiskBoundaryPath :
    Path (circleToPolygonDisk (1 : Circle))
      (circleToPolygonDisk (1 : Circle)) :=
  (ConstructionTargets.CircleUniversalCover.integerLoop 1).map
    continuous_circleToPolygonDisk

theorem torusRP2DiskBoundaryClass_eq_refl :
    (Path.Homotopic.Quotient.mk torusRP2DiskBoundaryPath :
      FundamentalGroup ConstructionTargets.Surfaces.Disk
        (circleToPolygonDisk (1 : Circle))) =
      Path.Homotopic.Quotient.refl (circleToPolygonDisk (1 : Circle)) := by
  letI : ContractibleSpace ConstructionTargets.Surfaces.Disk :=
    Metric.contractibleSpace_closedBall (by norm_num : (0 : ℝ) ≤ 1)
  exact Subsingleton.elim _ _

/-- The geometric boundary loop dies after inclusion into the polygon
quotient.  This is the disk-side input to the forward kernel inclusion in
based van Kampen. -/
theorem torusRP2DiskBoundaryPath_map_quotient_eq_one :
    FundamentalGroup.map
        (⟨torusRP2PairingData.quotientMap,
          torusRP2PairingData.continuous_quotientMap⟩ :
          C(ConstructionTargets.Surfaces.Disk, torusRP2PairingData.Space))
        (circleToPolygonDisk (1 : Circle))
        (Path.Homotopic.Quotient.mk torusRP2DiskBoundaryPath) = 1 := by
  rw [torusRP2DiskBoundaryClass_eq_refl]
  rfl

theorem torusRP2DiskBoundaryBase_eq_skeletonBase :
    torusRP2PairingData.quotientMap (circleToPolygonDisk (1 : Circle)) =
      torusRP2SkeletonToPairingSpace torusRP2SkeletonBase := by
  have hs : polygonBoundarySkeletonLoop torusRP2PairingData 1 =
      torusRP2SkeletonBase := by
    apply torusRP2PairingData.skeletonHomeomorphWedge.injective
    rw [torusRP2SkeletonHomeomorphWedge_base]
    exact polygonBoundaryWedgeLoop_one torusRP2PairingData
  exact congrArg Subtype.val hs

theorem torusRP2PolygonBoundarySkeletonLoop_one :
    polygonBoundarySkeletonLoop torusRP2PairingData 1 =
      torusRP2SkeletonBase := by
  apply torusRP2PairingData.skeletonHomeomorphWedge.injective
  rw [torusRP2SkeletonHomeomorphWedge_base]
  exact polygonBoundaryWedgeLoop_one torusRP2PairingData

/-- The literal once-around boundary path in the polygon skeleton, with its
endpoints transported to the fixed skeleton basepoint. -/
noncomputable def torusRP2LiteralSkeletonBoundaryPath :
    Path torusRP2SkeletonBase torusRP2SkeletonBase :=
  ((ConstructionTargets.CircleUniversalCover.integerLoop 1).map
    (polygonBoundarySkeletonLoop torusRP2PairingData).continuous).cast
      torusRP2PolygonBoundarySkeletonLoop_one.symm
      torusRP2PolygonBoundarySkeletonLoop_one.symm

theorem torusRP2LiteralSkeletonBoundaryPath_apply (t : Set.Icc (0 : ℝ) 1) :
    torusRP2LiteralSkeletonBoundaryPath t =
      polygonBoundarySkeletonLoop torusRP2PairingData
        (ConstructionTargets.CircleUniversalCover.integerLoop 1 t) := by
  exact congrFun (Path.cast_coe _ _ _) t

theorem torusRP2PolygonBoundaryIntegerLoopPath_apply
    (t : Set.Icc (0 : ℝ) 1) :
    polygonBoundaryIntegerLoopPath torusRP2PairingData t =
      polygonBoundaryWedgeLoop torusRP2PairingData
        (ConstructionTargets.CircleUniversalCover.integerLoop 1 t) := by
  exact congrFun (Path.cast_coe _ _ _) t

/-- Mapping the literal skeleton boundary path to wedge coordinates gives
the previously normalized boundary path exactly. -/
theorem torusRP2LiteralSkeletonBoundaryPath_map_wedge :
    (torusRP2LiteralSkeletonBoundaryPath.map
      torusRP2PairingData.skeletonHomeomorphWedge.continuous).cast
        torusRP2SkeletonHomeomorphWedge_base.symm
        torusRP2SkeletonHomeomorphWedge_base.symm =
      polygonBoundaryIntegerLoopPath torusRP2PairingData := by
  ext t
  rw [congrFun (Path.cast_coe _ _ _) t]
  change torusRP2PairingData.skeletonHomeomorphWedge
      (torusRP2LiteralSkeletonBoundaryPath t) = _
  rw [torusRP2LiteralSkeletonBoundaryPath_apply,
    torusRP2PolygonBoundaryIntegerLoopPath_apply]
  rfl

theorem torusRP2SkeletonBoundaryClass_eq_literal :
    torusRP2SkeletonFundamentalGroupEquivWedge.symm
        (Path.Homotopic.Quotient.mk
          (polygonBoundaryIntegerLoopPath torusRP2PairingData)) =
      Path.Homotopic.Quotient.mk torusRP2LiteralSkeletonBoundaryPath := by
  apply torusRP2SkeletonFundamentalGroupEquivWedge.injective
  rw [torusRP2SkeletonFundamentalGroupEquivWedge.apply_symm_apply]
  change _ = FundamentalGroup.mapOfEq
      ⟨torusRP2PairingData.skeletonHomeomorphWedge,
        torusRP2PairingData.skeletonHomeomorphWedge.continuous⟩
      torusRP2SkeletonHomeomorphWedge_base
      (Path.Homotopic.Quotient.mk torusRP2LiteralSkeletonBoundaryPath)
  rw [FundamentalGroup.mapOfEq_apply]
  exact congrArg Path.Homotopic.Quotient.mk
    torusRP2LiteralSkeletonBoundaryPath_map_wedge.symm

theorem torusRP2LiteralSkeletonBoundary_map_eq_diskBoundary_map :
    torusRP2SkeletonToPairingSpacePiOne
        (Path.Homotopic.Quotient.mk torusRP2LiteralSkeletonBoundaryPath) =
      FundamentalGroup.mapOfEq
        (⟨torusRP2PairingData.quotientMap,
          torusRP2PairingData.continuous_quotientMap⟩ :
          C(ConstructionTargets.Surfaces.Disk, torusRP2PairingData.Space))
        torusRP2DiskBoundaryBase_eq_skeletonBase
        (Path.Homotopic.Quotient.mk torusRP2DiskBoundaryPath) := by
  rw [torusRP2SkeletonToPairingSpacePiOne, FundamentalGroup.map_apply,
    FundamentalGroup.mapOfEq_apply]
  apply Path.Homotopic.Quotient.eq.mpr
  convert Path.Homotopic.refl _ using 1

/-- Exact typed identification of the skeleton attaching class with the
disk boundary class, including all basepoint transports. -/
theorem torusRP2SkeletonBoundary_map_eq_diskBoundary_map :
    torusRP2SkeletonToPairingSpacePiOne
        (torusRP2SkeletonFundamentalGroupEquivWedge.symm
          (Path.Homotopic.Quotient.mk
            (polygonBoundaryIntegerLoopPath torusRP2PairingData))) =
      FundamentalGroup.mapOfEq
        (⟨torusRP2PairingData.quotientMap,
          torusRP2PairingData.continuous_quotientMap⟩ :
          C(ConstructionTargets.Surfaces.Disk, torusRP2PairingData.Space))
        torusRP2DiskBoundaryBase_eq_skeletonBase
        (Path.Homotopic.Quotient.mk torusRP2DiskBoundaryPath) := by
  rw [torusRP2SkeletonBoundaryClass_eq_literal]
  exact torusRP2LiteralSkeletonBoundary_map_eq_diskBoundary_map

theorem torusRP2SkeletonBoundary_map_eq_one :
    torusRP2SkeletonToPairingSpacePiOne
        (torusRP2SkeletonFundamentalGroupEquivWedge.symm
          (Path.Homotopic.Quotient.mk
            (polygonBoundaryIntegerLoopPath torusRP2PairingData))) = 1 := by
  rw [torusRP2SkeletonBoundary_map_eq_diskBoundary_map,
    torusRP2DiskBoundaryClass_eq_refl]
  exact map_one _

theorem torusRP2GeometricBoundary_normalClosure_le_kernel :
    Subgroup.normalClosure ({
        torusRP2SkeletonFundamentalGroupEquivWedge.symm
          (Path.Homotopic.Quotient.mk
            (polygonBoundaryIntegerLoopPath torusRP2PairingData))} :
      Set (FundamentalGroup torusRP2PairingData.skeleton
        torusRP2SkeletonBase)) ≤
      MonoidHom.ker torusRP2SkeletonToPairingSpacePiOne := by
  apply Subgroup.normalClosure_le_normal
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  exact torusRP2SkeletonBoundary_map_eq_one

/-- Choose the basis change forced by the (globally constant) orientation of
the normalized circle generator. -/
noncomputable def torusRP2BoundaryBasisEquiv :
    FreeGroup (Fin 3) ≃* FreeGroup (Fin 3) :=
  if circleIntegerLoopOneCoordinate = 1 then
    torusRP2PositiveBoundaryBasisEquiv
  else torusRP2NegativeBoundaryBasisEquiv

/-- The canonical free-group map whose quotient is computed by based van
Kampen: basis coordinates, then the skeleton, then the polygon quotient. -/
noncomputable def torusRP2BoundaryFreeGroupMap :
    FreeGroup (Fin 3) →*
      FundamentalGroup torusRP2PairingData.Space
        (torusRP2SkeletonToPairingSpace torusRP2SkeletonBase) :=
  torusRP2SkeletonToPairingSpacePiOne.comp
    (torusRP2SkeletonFinFreeGroupMap.comp
      torusRP2BoundaryBasisEquiv.toMonoidHom)

theorem torusRP2Relator_normalClosure_le_kernel :
    Subgroup.normalClosure ({torusRP2FrozenRelator} :
      Set (FreeGroup (Fin 3))) ≤
      MonoidHom.ker torusRP2BoundaryFreeGroupMap := by
  apply Subgroup.normalClosure_le_normal
  intro g hg
  rw [Set.mem_singleton_iff.mp hg]
  change torusRP2SkeletonToPairingSpacePiOne
      (torusRP2SkeletonFinFreeGroupMap
        (torusRP2BoundaryBasisEquiv torusRP2FrozenRelator)) = 1
  apply torusRP2GeometricBoundary_normalClosure_le_kernel
  rw [← torusRP2AttachingWord]
  apply Subgroup.subset_normalClosure
  by_cases h : circleIntegerLoopOneCoordinate = 1
  · simp only [torusRP2BoundaryBasisEquiv, h, if_pos]
    rfl
  · simp only [torusRP2BoundaryBasisEquiv, h, if_neg]
    rfl

theorem torusRP2BoundaryFreeGroupMap_surjective
    (h : Function.Surjective torusRP2SkeletonToPairingSpacePiOne) :
    Function.Surjective torusRP2BoundaryFreeGroupMap := by
  exact h.comp (torusRP2SkeletonFinFreeGroupMap_surjective.comp
    torusRP2BoundaryBasisEquiv.surjective)

/-- The proved two-open fundamental-groupoid pseudopushout, specialized to
the radial cover of the torus-crosscap polygon.  This is the exact cover-level
input needed to derive surjectivity and the reverse kernel inclusion. -/
noncomputable def torusRP2PolygonFundamentalGroupoidPseudopushout
    (C : Type) [CategoryTheory.Category C] :
    (FundamentalGroupoid torusRP2PairingData.Space ⥤ C) ≌
      @PseudoFunctorCocone torusRP2PairingData.Space _
        (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer C _ :=
  twoOpenFundamentalGroupoidPseudopushoutEquivalence
    (openCover torusRP2PairingData).inner_open
    (openCover torusRP2PairingData).outer_open
    (openCover torusRP2PairingData).cover

/-- Reconstruct the identity fundamental-groupoid functor from its two radial
cover restrictions. -/
noncomputable def torusRP2PolygonPseudopushoutReconstructedIdentity :
    FundamentalGroupoid torusRP2PairingData.Space ⥤
      FundamentalGroupoid torusRP2PairingData.Space :=
  (torusRP2PolygonFundamentalGroupoidPseudopushout
    (FundamentalGroupoid torusRP2PairingData.Space)).inverse.obj
      ((torusRP2PolygonFundamentalGroupoidPseudopushout
        (FundamentalGroupoid torusRP2PairingData.Space)).functor.obj
          (𝟭 (FundamentalGroupoid torusRP2PairingData.Space)))

/-- Unit identifying the literal identity functor with its reconstructed
radial-cover functor. -/
noncomputable def torusRP2PolygonPseudopushoutReconstructionUnit :
    (𝟭 (FundamentalGroupoid torusRP2PairingData.Space)) ≅
      torusRP2PolygonPseudopushoutReconstructedIdentity :=
  (torusRP2PolygonFundamentalGroupoidPseudopushout
    (FundamentalGroupoid torusRP2PairingData.Space)).unitIso.app _

/-- Every polygon fundamental-groupoid arrow is conjugate, through the
pseudopushout unit, to the arrow reconstructed from the two cover pieces. -/
theorem torusRP2PolygonPseudopushout_arrow_eq_reconstructed
    {x y : FundamentalGroupoid torusRP2PairingData.Space} (g : x ⟶ y) :
    g = torusRP2PolygonPseudopushoutReconstructionUnit.hom.app x ≫
      torusRP2PolygonPseudopushoutReconstructedIdentity.map g ≫
      torusRP2PolygonPseudopushoutReconstructionUnit.inv.app y := by
  rw [← Category.assoc,
    ← torusRP2PolygonPseudopushoutReconstructionUnit.hom.naturality g]
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

/-- The inner member of the exact radial cover is contractible. -/
theorem torusRP2PolygonInnerContractibleSpace :
    ContractibleSpace
      {q // q ∈ (openCover torusRP2PairingData).inner} := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨(openCover torusRP2PairingData).center,
    ⟨(openCover torusRP2PairingData).contraction.homotopy⟩⟩

/-- Any two fixed-endpoint arrows through the contractible inner cover piece
are equal.  This is the replacement principle used to eliminate inner runs
from a radial-cover subdivision. -/
theorem torusRP2PolygonInnerFundamentalGroupoid_hom_subsingleton
    (x y : {q // q ∈ (openCover torusRP2PairingData).inner}) :
    Subsingleton (FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) := by
  letI : ContractibleSpace
      {q // q ∈ (openCover torusRP2PairingData).inner} :=
    torusRP2PolygonInnerContractibleSpace
  letI : SimplyConnectedSpace
      {q // q ∈ (openCover torusRP2PairingData).inner} :=
    SimplyConnectedSpace.ofContractible _
  change Subsingleton (Path.Homotopic.Quotient x y)
  infer_instance

theorem torusRP2PolygonInner_pathClass_eq
    {x y : {q // q ∈ (openCover torusRP2PairingData).inner}}
    (p q : Path x y) :
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) = ⟦q⟧ := by
  letI : ContractibleSpace
      {q // q ∈ (openCover torusRP2PairingData).inner} :=
    torusRP2PolygonInnerContractibleSpace
  letI : SimplyConnectedSpace
      {q // q ∈ (openCover torusRP2PairingData).inner} :=
    SimplyConnectedSpace.ofContractible _
  exact Quotient.sound (SimplyConnectedSpace.paths_homotopic p q)

theorem torusRP2PolygonOverlapPathConnectedSpace :
    PathConnectedSpace (overlapOpen torusRP2PairingData.Rel) := by
  letI : PathConnectedSpace (Set.Ioo (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo 0 1).isPathConnected ⟨1 / 2, by norm_num⟩)
  letI : PathConnectedSpace (Set.Ioo (0 : ℝ) 1 × Circle) :=
    ⟨⟨(⟨1 / 2, by norm_num⟩, 1)⟩, fun x y ↦
      ⟨(PathConnectedSpace.joined x.1 y.1).some.prod
        (PathConnectedSpace.joined x.2 y.2).some⟩⟩
  exact (openCover torusRP2PairingData).overlap_homeomorph.symm.surjective.pathConnectedSpace
    (openCover torusRP2PairingData).overlap_homeomorph.symm.continuous

noncomputable def torusRP2PolygonOverlapToOuter :
    C(overlapOpen torusRP2PairingData.Rel,
      {q // q ∈ (openCover torusRP2PairingData).outer}) :=
  ⟨fun z ↦ ⟨z.1, (by
      have hz : z.1 ∈ (openCover torusRP2PairingData).inner ∩
          (openCover torusRP2PairingData).outer := by
        rw [← (openCover torusRP2PairingData).overlap_eq]
        exact z.2
      exact hz.2)⟩,
    Continuous.subtype_mk continuous_subtype_val (fun z ↦ by
      have hz : z.1 ∈ (openCover torusRP2PairingData).inner ∩
          (openCover torusRP2PairingData).outer := by
        rw [← (openCover torusRP2PairingData).overlap_eq]
        exact z.2
      exact hz.2)⟩

noncomputable def torusRP2PolygonOverlapToInner :
    C(overlapOpen torusRP2PairingData.Rel,
      {q // q ∈ (openCover torusRP2PairingData).inner}) :=
  ⟨fun z ↦ ⟨z.1, (by
      have hz : z.1 ∈ (openCover torusRP2PairingData).inner ∩
          (openCover torusRP2PairingData).outer := by
        rw [← (openCover torusRP2PairingData).overlap_eq]
        exact z.2
      exact hz.1)⟩,
    Continuous.subtype_mk continuous_subtype_val (fun z ↦ by
      have hz : z.1 ∈ (openCover torusRP2PairingData).inner ∩
          (openCover torusRP2PairingData).outer := by
        rw [← (openCover torusRP2PairingData).overlap_eq]
        exact z.2
      exact hz.1)⟩

noncomputable def torusRP2PolygonInnerToSpace :
    C({q // q ∈ (openCover torusRP2PairingData).inner},
      torusRP2PairingData.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

noncomputable def torusRP2PolygonOuterToSpace :
    C({q // q ∈ (openCover torusRP2PairingData).outer},
      torusRP2PairingData.Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- An inner path between overlap points is equal in the ambient groupoid to
an overlap path routed through the outer radial piece. -/
theorem torusRP2PolygonInner_ambientPathClass_eq_outerOverlapReplacement
    (x y : overlapOpen torusRP2PairingData.Rel)
    (p : Path (torusRP2PolygonOverlapToInner x)
      (torusRP2PolygonOverlapToInner y)) :
    ∃ q : Path x y,
      (⟦p.map torusRP2PolygonInnerToSpace.continuous⟧ :
          FundamentalGroupoid.mk x.1 ⟶ FundamentalGroupoid.mk y.1) =
        ⟦(q.map torusRP2PolygonOverlapToOuter.continuous).map
          torusRP2PolygonOuterToSpace.continuous⟧ := by
  letI : PathConnectedSpace (overlapOpen torusRP2PairingData.Rel) :=
    torusRP2PolygonOverlapPathConnectedSpace
  let q : Path x y := PathConnectedSpace.somePath x y
  refine ⟨q, ?_⟩
  have hq := torusRP2PolygonInner_pathClass_eq p
    (q.map torusRP2PolygonOverlapToInner.continuous)
  have hmap := congrArg
    (fun z : FundamentalGroupoid.mk (torusRP2PolygonOverlapToInner x) ⟶
        FundamentalGroupoid.mk (torusRP2PolygonOverlapToInner y) ↦
      (FundamentalGroupoid.map torusRP2PolygonInnerToSpace).map z) hq
  simpa [torusRP2PolygonInnerToSpace, torusRP2PolygonOverlapToInner,
    torusRP2PolygonOuterToSpace, torusRP2PolygonOverlapToOuter] using hmap

/-- An ambient path forming an inner subdivision run can be normalized using
only its endpoint overlap membership and its inner-piece range proof. -/
theorem torusRP2PolygonInnerRun_exists_outerOverlapReplacement
    {x y : torusRP2PairingData.Space}
    (hx : x ∈ (openCover torusRP2PairingData).inner ∩
      (openCover torusRP2PairingData).outer)
    (hy : y ∈ (openCover torusRP2PairingData).inner ∩
      (openCover torusRP2PairingData).outer)
    (p : Path x y)
    (hp : ∀ t, p t ∈ (openCover torusRP2PairingData).inner) :
    ∃ q : Path
        (⟨x, by rw [(openCover torusRP2PairingData).overlap_eq]; exact hx⟩ :
          overlapOpen torusRP2PairingData.Rel)
        (⟨y, by rw [(openCover torusRP2PairingData).overlap_eq]; exact hy⟩ :
          overlapOpen torusRP2PairingData.Rel),
      (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) =
        ⟦(q.map torusRP2PolygonOverlapToOuter.continuous).map
          torusRP2PolygonOuterToSpace.continuous⟧ := by
  let xo : overlapOpen torusRP2PairingData.Rel := ⟨x, by
    rw [(openCover torusRP2PairingData).overlap_eq]
    exact hx⟩
  let yo : overlapOpen torusRP2PairingData.Rel := ⟨y, by
    rw [(openCover torusRP2PairingData).overlap_eq]
    exact hy⟩
  let pInner : Path (torusRP2PolygonOverlapToInner xo)
      (torusRP2PolygonOverlapToInner yo) :=
    { toFun := fun t ↦ ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  obtain ⟨q, hq⟩ :=
    torusRP2PolygonInner_ambientPathClass_eq_outerOverlapReplacement xo yo pInner
  refine ⟨q, ?_⟩
  simpa [pInner, torusRP2PolygonInnerToSpace,
    torusRP2PolygonOuterToSpace] using hq

theorem torusRP2_path_concat_mem_of_piece_mem
    {X : Type*} [TopologicalSpace X] {U : Set X} {n : ℕ}
    (point : Fin (n + 2) → X)
    (F : (k : Fin (n + 1)) → Path (point k.castSucc) (point k.succ))
    (hF : ∀ k t, F k t ∈ U) :
    ∀ t, Path.concat point F t ∈ U := by
  induction n with
  | zero =>
      intro t
      rw [Path.concat_succ, Path.concat_zero]
      have ht : ((Path.concat (point ∘ Fin.castSucc)
          (fun k ↦ F k.castSucc)).trans (F (Fin.last 0))) t ∈
          Set.range ((Path.concat (point ∘ Fin.castSucc)
            (fun k ↦ F k.castSucc)).trans (F (Fin.last 0))) :=
        Set.mem_range_self t
      rw [Path.concat_zero, Path.trans_range] at ht
      rcases ht with ht | ht
      · rcases ht with ⟨s, hs⟩
        have hm : (Path.refl ((point ∘ Fin.castSucc) 0)) s ∈ U := by
          change point 0 ∈ U
          convert hF 0 0 using 1
          rw [(F 0).source]
          congr 1
        exact hs ▸ hm
      · rcases ht with ⟨s, hs⟩
        exact hs ▸ hF (Fin.last 0) s
  | succ n ih =>
      intro t
      rw [Path.concat_succ]
      change ((Path.concat (point ∘ Fin.castSucc)
        (fun k ↦ F k.castSucc)).trans (F (Fin.last (n + 1)))) t ∈ U
      have ht : ((Path.concat (point ∘ Fin.castSucc)
          (fun k ↦ F k.castSucc)).trans (F (Fin.last (n + 1)))) t ∈
          Set.range ((Path.concat (point ∘ Fin.castSucc)
            (fun k ↦ F k.castSucc)).trans (F (Fin.last (n + 1)))) :=
        Set.mem_range_self t
      rw [Path.trans_range] at ht
      rcases ht with ⟨s, hs⟩ | ⟨s, hs⟩
      · exact hs ▸ ih (point ∘ Fin.castSucc) (fun k ↦ F k.castSucc)
          (fun k u ↦ hF k.castSucc u) s
      · exact hs ▸ hF (Fin.last (n + 1)) s

/-- A whole nonempty dependent inner block has one overlap representative
routed through the outer radial piece. -/
theorem torusRP2PolygonInnerBlock_exists_outerOverlapReplacement
    {n : ℕ}
    (point : Fin (n + 2) → torusRP2PairingData.Space)
    (F : (k : Fin (n + 1)) → Path (point k.castSucc) (point k.succ))
    (hx : point 0 ∈ (openCover torusRP2PairingData).inner ∩
      (openCover torusRP2PairingData).outer)
    (hy : point (Fin.last (n + 1)) ∈
      (openCover torusRP2PairingData).inner ∩
      (openCover torusRP2PairingData).outer)
    (hF : ∀ k t, F k t ∈ (openCover torusRP2PairingData).inner) :
    ∃ q : Path
        (⟨point 0, by rw [(openCover torusRP2PairingData).overlap_eq]; exact hx⟩ :
          overlapOpen torusRP2PairingData.Rel)
        (⟨point (Fin.last (n + 1)), by
          rw [(openCover torusRP2PairingData).overlap_eq]; exact hy⟩ :
          overlapOpen torusRP2PairingData.Rel),
      (⟦Path.concat point F⟧ : FundamentalGroupoid.mk (point 0) ⟶
          FundamentalGroupoid.mk (point (Fin.last (n + 1)))) =
        ⟦(q.map torusRP2PolygonOverlapToOuter.continuous).map
          torusRP2PolygonOuterToSpace.continuous⟧ := by
  exact torusRP2PolygonInnerRun_exists_outerOverlapReplacement hx hy
    (Path.concat point F) (torusRP2_path_concat_mem_of_piece_mem point F hF)

/-- Pointwise equality of the normalized factors propagates through the
dependent finite concatenation used to reassemble subdivision blocks. -/
theorem torusRP2_pathHomotopicQuotient_concat_eq_of_pieceClass_eq
    {X : Type*} [TopologicalSpace X] {n : ℕ}
    (point : Fin (n + 1) → X)
    (F G : (k : Fin n) → Path (point k.castSucc) (point k.succ))
    (h : ∀ k, (⟦F k⟧ : Path.Homotopic.Quotient _ _) = ⟦G k⟧) :
    (⟦Path.concat point F⟧ : Path.Homotopic.Quotient _ _) =
      ⟦Path.concat point G⟧ := by
  apply Quotient.sound
  exact Path.Homotopic.concat_hcomp point F G
    (fun k ↦ Quotient.eq.mp (h k))

/-- Replacing every piece of a subordinate subdivision by an equal path
class reconstructs the class of the original path. -/
theorem torusRP2_subdivision_quotient_eq_concat_of_pieceClass_eq
    {X : Type*} [TopologicalSpace X]
    {x y : X} {p : Path x y} {U V : Set X}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p U V)
    (G : (k : Fin (S.n + 1)) →
      Path (S.point k.castSucc) (S.point k.succ))
    (h : ∀ k, (⟦S.piece k⟧ : Path.Homotopic.Quotient _ _) = ⟦G k⟧) :
    (⟦p.cast S.point_zero S.point_last⟧ : Path.Homotopic.Quotient _ _) =
      ⟦Path.concat S.point G⟧ := by
  calc
    _ = ⟦Path.concat S.point S.piece⟧ := S.quotient_concat_eq.symm
    _ = _ := torusRP2_pathHomotopicQuotient_concat_eq_of_pieceClass_eq
      S.point S.piece G h

/-- The maximal constant-side runs of a subordinate polygon subdivision meet
at literal common vertices in the radial overlap.  This imports the generic
finite-run certificate already proved for two-open subdivisions, so the next
normalization step may choose one outer replacement for each inner run. -/
theorem torusRP2_subdivision_runPartition_boundary_spec
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer) :
    (boolSideRunPartition S.side).IsChain
      fun a b => ∀ (ha : a ≠ []) (hb : b ≠ []),
        S.point (a.getLast ha).succ = S.point (b.head hb).castSucc ∧
          S.point (b.head hb).castSucc ∈
            (openCover torusRP2PairingData).inner ∩
              (openCover torusRP2PairingData).outer := by
  exact pathTwoOpenSubdivision_runPartition_boundary_spec S

/-- Every maximal run in a torus-crosscap radial subdivision has a single
ambient representative whose range lies in the outer piece. -/
theorem torusRP2_subdivisionRun_exists_outerRepresentative
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    ∃ q : Path (pathTwoOpenSubdivisionRunBlockPoint S i 0)
        (pathTwoOpenSubdivisionRunBlockPoint S i
          (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1))),
      (∀ t, q t ∈ (openCover torusRP2PairingData).outer) ∧
      (⟦Path.concat (pathTwoOpenSubdivisionRunBlockPoint S i)
          (pathTwoOpenSubdivisionRunBlockPiece S i)⟧ :
        FundamentalGroupoid.mk (pathTwoOpenSubdivisionRunBlockPoint S i 0) ⟶
          FundamentalGroupoid.mk (pathTwoOpenSubdivisionRunBlockPoint S i
            (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)))) =
        ⟦q⟧ := by
  let side := S.side ((pathTwoOpenSubdivisionRunFamily S i).head
    (pathTwoOpenSubdivisionRunFamily_ne_nil S i))
  have hbound' : pathTwoOpenSubdivisionRunStart S i +
      (pathTwoOpenSubdivisionRunPredLength S i + 1) ≤ S.n + 1 := by
    rw [pathTwoOpenSubdivisionRunPredLength_add_one]
    exact pathTwoOpenSubdivisionRunStart_add_length_le S i
  by_cases hs : side = true
  · have hF := pathTwoOpenSubdivisionRunBlockPiece_mem_inner_of_side_eq_true S i hs
    have hxInner : pathTwoOpenSubdivisionRunBlockPoint S i 0 ∈
        (openCover torusRP2PairingData).inner := by
      have hz : (0 : Fin (pathTwoOpenSubdivisionRunPredLength S i + 2)) =
          (0 : Fin (pathTwoOpenSubdivisionRunPredLength S i + 1)).castSucc := rfl
      rw [hz]
      rw [← (pathTwoOpenSubdivisionRunBlockPiece S i 0).source]
      exact hF 0 0
    have hyInner : pathTwoOpenSubdivisionRunBlockPoint S i
        (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)) ∈
        (openCover torusRP2PairingData).inner := by
      have hi : (Fin.last (pathTwoOpenSubdivisionRunPredLength S i)).succ =
          Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1) := by
        apply Fin.ext
        simp
      rw [← hi, ← (pathTwoOpenSubdivisionRunBlockPiece S i
        (Fin.last (pathTwoOpenSubdivisionRunPredLength S i))).target]
      exact hF (Fin.last (pathTwoOpenSubdivisionRunPredLength S i)) 1
    have hxOuter : pathTwoOpenSubdivisionRunBlockPoint S i 0 ∈
        (openCover torusRP2PairingData).outer := by
      rw [← pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
        S hx hy i]
      exact (pathTwoOpenSubdivisionOuterRunBoundaryFamily _ _ _ _).property
    have hyOuter : pathTwoOpenSubdivisionRunBlockPoint S i
        (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)) ∈
        (openCover torusRP2PairingData).outer := by
      rw [← pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
        S hx hy i]
      exact (pathTwoOpenSubdivisionOuterRunBoundaryFamily _ _ _ _).property
    obtain ⟨q, hq⟩ := torusRP2PolygonInnerBlock_exists_outerOverlapReplacement
      (pathTwoOpenSubdivisionRunBlockPoint S i)
      (pathTwoOpenSubdivisionRunBlockPiece S i)
      ⟨hxInner, hxOuter⟩ ⟨hyInner, hyOuter⟩ hF
    refine ⟨(q.map torusRP2PolygonOverlapToOuter.continuous).map
      torusRP2PolygonOuterToSpace.continuous, ?_, hq⟩
    intro t
    exact ((q.map torusRP2PolygonOverlapToOuter.continuous) t).property
  · have hs' : side = false := Bool.eq_false_of_not_eq_true hs
    have hF := pathTwoOpenSubdivisionRunBlockPiece_mem_outer_of_side_eq_false S i hs'
    obtain ⟨q, hq⟩ := path_concat_exists_subtype_path
      (pathTwoOpenSubdivisionRunBlockPoint S i)
      (pathTwoOpenSubdivisionRunBlockPiece S i) hF
    refine ⟨q.map torusRP2PolygonOuterToSpace.continuous, ?_, ?_⟩
    · intro t
      exact (q t).property
    · exact congrArg Path.Homotopic.Quotient.mk hq.symm

/-- A maximal-run representative rebased at consecutive entries of the
canonical outer boundary family. -/
theorem torusRP2_subdivisionRun_exists_outerBoundaryPath
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    ∃ q : Path
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.castSucc)
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.succ),
      Path.Homotopic.Quotient.cast
          (⟦Path.concat (pathTwoOpenSubdivisionRunBlockPoint S i)
            (pathTwoOpenSubdivisionRunBlockPiece S i)⟧)
          (pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
            S hx hy i)
          (pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
            S hx hy i) =
        ⟦q.map torusRP2PolygonOuterToSpace.continuous⟧ := by
  obtain ⟨r, hrange, hr⟩ :=
    torusRP2_subdivisionRun_exists_outerRepresentative S hx hy i
  let r' : Path
      (⟨pathTwoOpenSubdivisionRunBlockPoint S i 0, by simpa using hrange 0⟩ :
        {z // z ∈ (openCover torusRP2PairingData).outer})
      (⟨pathTwoOpenSubdivisionRunBlockPoint S i
          (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)),
        by simpa using hrange 1⟩ :
        {z // z ∈ (openCover torusRP2PairingData).outer}) :=
    { toFun := fun t => ⟨r t, hrange t⟩
      continuous_toFun := r.continuous.subtype_mk _
      source' := Subtype.ext r.source
      target' := Subtype.ext r.target }
  have hs : pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.castSucc =
      (⟨pathTwoOpenSubdivisionRunBlockPoint S i 0, by simpa using hrange 0⟩ :
        {z // z ∈ (openCover torusRP2PairingData).outer}) := by
    apply Subtype.ext
    exact pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
      S hx hy i
  have ht : pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.succ =
      (⟨pathTwoOpenSubdivisionRunBlockPoint S i
          (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)),
        by simpa using hrange 1⟩ :
        {z // z ∈ (openCover torusRP2PairingData).outer}) := by
    apply Subtype.ext
    exact pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
      S hx hy i
  refine ⟨r'.cast hs ht, ?_⟩
  rw [hr]
  change ⟦r.cast _ _⟧ = _
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact (congrFun (Path.cast_coe r _ _) t).trans
    (congrArg Subtype.val (congrFun (Path.cast_coe r' hs ht) t)).symm

noncomputable def torusRP2_subdivisionOuterRunPath
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) : Path
      (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.castSucc)
      (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.succ) :=
  Classical.choose
    (torusRP2_subdivisionRun_exists_outerBoundaryPath S hx hy i)

theorem torusRP2_subdivisionOuterRunPath_class
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    Path.Homotopic.Quotient.cast
        (⟦Path.concat (pathTwoOpenSubdivisionRunBlockPoint S i)
          (pathTwoOpenSubdivisionRunBlockPiece S i)⟧)
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
          S hx hy i)
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
          S hx hy i) =
      ⟦(torusRP2_subdivisionOuterRunPath S hx hy i).map
        torusRP2PolygonOuterToSpace.continuous⟧ :=
  Classical.choose_spec
    (torusRP2_subdivisionRun_exists_outerBoundaryPath S hx hy i)

/-- Folding all chosen maximal-run representatives produces one outer path
with the ambient class of their ordered dependent concatenation. -/
theorem torusRP2_subdivisionRunFold_exists_outerPath
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer) :
    ∃ q : Path
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy 0)
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy
          (Fin.last (boolSideRunPartition S.side).length)),
      (⟦Path.concat
          (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
            torusRP2PairingData.Space))
          (fun i => (Path.concat (pathTwoOpenSubdivisionRunBlockPoint S i)
            (pathTwoOpenSubdivisionRunBlockPiece S i)).cast
              (pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
                S hx hy i)
              (pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
                S hx hy i))⟧ : Path.Homotopic.Quotient _ _) =
        ⟦q.map torusRP2PolygonOuterToSpace.continuous⟧ := by
  refine ⟨Path.concat (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy)
    (torusRP2_subdivisionOuterRunPath S hx hy), ?_⟩
  change _ = ⟦(Path.concat
    (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy)
    (torusRP2_subdivisionOuterRunPath S hx hy)).map
      continuous_subtype_val⟧
  rw [path_concat_map_subtype]
  exact torusRP2_pathHomotopicQuotient_concat_eq_of_pieceClass_eq
    (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
      torusRP2PairingData.Space))
    (fun i => (Path.concat (pathTwoOpenSubdivisionRunBlockPoint S i)
      (pathTwoOpenSubdivisionRunBlockPiece S i)).cast
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
          S hx hy i)
        (pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
          S hx hy i))
    (fun i => (torusRP2_subdivisionOuterRunPath S hx hy i).map
      torusRP2PolygonOuterToSpace.continuous)
    (torusRP2_subdivisionOuterRunPath_class S hx hy)

@[simp] theorem torusRP2_subdivisionOuterRunBoundaryFamily_zero
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer) :
    (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy 0 :
      torusRP2PairingData.Space) = S.point 0 := by
  simp [pathTwoOpenSubdivisionOuterRunBoundaryFamily,
    pathTwoOpenSubdivisionOuterRunBoundaryPoints,
    pathTwoOpenSubdivisionRunBoundaryPoints]

@[simp] theorem torusRP2_subdivisionOuterRunBoundaryFamily_last
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer) :
    (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy
      (Fin.last (boolSideRunPartition S.side).length) :
      torusRP2PairingData.Space) = S.point (Fin.last (S.n + 1)) := by
  rw [pathTwoOpenSubdivisionOuterRunBoundaryFamily_val]
  rw [← pathTwoOpenSubdivisionRunBoundaryPoints_getLast S]
  rw [List.getLast_eq_getElem]
  congr 1
  apply Fin.ext
  simp [pathTwoOpenSubdivisionRunBoundaryPoints_length]

/-- The folded outer representative rebased at the literal endpoints of the
original subdivision, preserving its ambient path class. -/
theorem torusRP2_subdivisionRunFold_exists_outerPath_at_endpoints
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer) :
    ∃ q : Path
        (⟨S.point 0, hx⟩ : {z // z ∈ (openCover torusRP2PairingData).outer})
        (⟨S.point (Fin.last (S.n + 1)), hy⟩ :
          {z // z ∈ (openCover torusRP2PairingData).outer}),
      Path.Homotopic.Quotient.cast
          (⟦Path.concat
            (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
              torusRP2PairingData.Space))
            (fun i => (Path.concat (pathTwoOpenSubdivisionRunBlockPoint S i)
              (pathTwoOpenSubdivisionRunBlockPiece S i)).cast
                (pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
                  S hx hy i)
                (pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
                  S hx hy i))⟧)
          (torusRP2_subdivisionOuterRunBoundaryFamily_zero S hx hy).symm
          (torusRP2_subdivisionOuterRunBoundaryFamily_last S hx hy).symm =
        ⟦q.map torusRP2PolygonOuterToSpace.continuous⟧ := by
  obtain ⟨q, hq⟩ := torusRP2_subdivisionRunFold_exists_outerPath S hx hy
  have hs : (⟨S.point 0, hx⟩ :
      {z // z ∈ (openCover torusRP2PairingData).outer}) =
      pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy 0 := by
    apply Subtype.ext
    exact (torusRP2_subdivisionOuterRunBoundaryFamily_zero S hx hy).symm
  have ht : (⟨S.point (Fin.last (S.n + 1)), hy⟩ :
      {z // z ∈ (openCover torusRP2PairingData).outer}) =
      pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy
        (Fin.last (boolSideRunPartition S.side).length) := by
    apply Subtype.ext
    exact (torusRP2_subdivisionOuterRunBoundaryFamily_last S hx hy).symm
  refine ⟨q.cast hs ht, ?_⟩
  rw [hq]
  change ⟦(q.map torusRP2PolygonOuterToSpace.continuous).cast _ _⟧ = _
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact (congrFun
      (Path.cast_coe (q.map torusRP2PolygonOuterToSpace.continuous) _ _) t).trans
    (congrArg Subtype.val (congrFun (Path.cast_coe q hs ht) t)).symm

/-- Each factor of a selected maximal run has the same path class after
rebasing it into the cumulative-prefix presentation used for regrouping. -/
theorem torusRP2_subdivisionRunBlockPiece_cast_eq_prefixBlockPiece
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length)
    (k : Fin (pathTwoOpenSubdivisionRunPredLength S i + 1)) :
    Path.Homotopic.Quotient.cast
        (⟦pathTwoOpenSubdivisionRunBlockPiece S i k⟧)
        (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
          k.castSucc).symm
        (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
          k.succ).symm =
      ⟦pathTwoOpenSubdivisionRunPrefixBlockPiece S i k⟧ := by
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  exact (congrFun (Path.cast_coe
      (pathTwoOpenSubdivisionRunBlockPiece S i k) _ _) t).trans
    (pathTwoOpenSubdivisionRunBlockPiece_eq_prefixBlockPiece S i k t)

/-- The dependent concatenation of a run, after each factor is rebased to
the cumulative-prefix vertices, has the class of the literal prefix block. -/
theorem torusRP2_subdivisionRunBlockConcat_cast_eq_prefixBlockConcat
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    (⟦Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
        (fun k => (pathTwoOpenSubdivisionRunBlockPiece S i k).cast
          (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
            k.castSucc).symm
          (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
            k.succ).symm)⟧ : Path.Homotopic.Quotient _ _) =
      ⟦Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
        (pathTwoOpenSubdivisionRunPrefixBlockPiece S i)⟧ := by
  exact torusRP2_pathHomotopicQuotient_concat_eq_of_pieceClass_eq
    (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
    (fun k => (pathTwoOpenSubdivisionRunBlockPiece S i k).cast
      (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
        k.castSucc).symm
      (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
        k.succ).symm)
    (pathTwoOpenSubdivisionRunPrefixBlockPiece S i)
    (torusRP2_subdivisionRunBlockPiece_cast_eq_prefixBlockPiece S i)

/-- Consecutive cumulative-prefix run blocks meet at the same subdivision
vertex, providing the endpoint equation for the outer regrouping fold. -/
theorem torusRP2_subdivisionRunPrefixBlock_adjacent
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i j : Fin (boolSideRunPartition S.side).length)
    (hij : j.val = i.val + 1) :
    pathTwoOpenSubdivisionRunPrefixBlockPoint S i
        (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)) =
      pathTwoOpenSubdivisionRunPrefixBlockPoint S j 0 := by
  unfold pathTwoOpenSubdivisionRunPrefixBlockPoint
  unfold pathTwoOpenSubdivisionBlockPoint
  apply congrArg S.point
  apply Fin.ext
  simp only [Fin.val_last, Fin.val_zero]
  rw [hij]
  exact pathTwoOpenSubdivisionRunPrefixLength_add_predLength S i

/-- Two consecutive cumulative-prefix blocks compose as the class of their
joined path after the next block is cast along the adjacency equation. -/
theorem torusRP2_subdivisionRunPrefixBlock_trans
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i j : Fin (boolSideRunPartition S.side).length)
    (hij : j.val = i.val + 1) :
    Path.Homotopic.Quotient.trans
        ⟦Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
          (pathTwoOpenSubdivisionRunPrefixBlockPiece S i)⟧
        ⟦(Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S j)
          (pathTwoOpenSubdivisionRunPrefixBlockPiece S j)).cast
            (torusRP2_subdivisionRunPrefixBlock_adjacent S i j hij) rfl⟧ =
      ⟦(Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
          (pathTwoOpenSubdivisionRunPrefixBlockPiece S i)).trans
        ((Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S j)
          (pathTwoOpenSubdivisionRunPrefixBlockPiece S j)).cast
            (torusRP2_subdivisionRunPrefixBlock_adjacent S i j hij) rfl)⟧ := by
  exact (Path.Homotopic.Quotient.mk_trans _ _).symm

/-- The terminal vertex of a cumulative-prefix run block is the subdivision
vertex at the cumulative length through that run. -/
theorem torusRP2_subdivisionRunPrefixBlockPoint_last
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    pathTwoOpenSubdivisionRunPrefixBlockPoint S i
        (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)) =
      S.point ⟨pathTwoOpenSubdivisionRunPrefixLength S (i.val + 1), by
        rw [← pathTwoOpenSubdivisionRunPrefixLength_add_predLength S i]
        have h := pathTwoOpenSubdivisionRunPrefixBlock_le S i
        omega⟩ := by
  unfold pathTwoOpenSubdivisionRunPrefixBlockPoint
  unfold pathTwoOpenSubdivisionBlockPoint
  apply congrArg S.point
  apply Fin.ext
  simp only [Fin.val_last]
  exact pathTwoOpenSubdivisionRunPrefixLength_add_predLength S i

/-- The initial vertex of a cumulative-prefix run block is the subdivision
vertex after all strictly preceding runs. -/
theorem torusRP2_subdivisionRunPrefixBlockPoint_zero
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    pathTwoOpenSubdivisionRunPrefixBlockPoint S i 0 =
      S.point ⟨pathTwoOpenSubdivisionRunPrefixLength S i.val, by
        have h := pathTwoOpenSubdivisionRunPrefixBlock_le S i
        omega⟩ := by
  rfl

/-- The global outer-boundary family and the cumulative-prefix presentation
of each run have the same source endpoint. -/
theorem torusRP2_subdivisionOuterRunBoundaryFamily_castSucc_eq_prefixBlockPoint_zero
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.castSucc :
        torusRP2PairingData.Space) =
      pathTwoOpenSubdivisionRunPrefixBlockPoint S i 0 :=
  (pathTwoOpenSubdivisionOuterRunBoundaryFamily_castSucc_eq_runBlockPoint_zero
    S hx hy i).trans
      (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i 0)

/-- The global outer-boundary family and the cumulative-prefix presentation
of each run have the same target endpoint. -/
theorem torusRP2_subdivisionOuterRunBoundaryFamily_succ_eq_prefixBlockPoint_last
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.succ :
        torusRP2PairingData.Space) =
      pathTwoOpenSubdivisionRunPrefixBlockPoint S i
        (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)) :=
  (pathTwoOpenSubdivisionOuterRunBoundaryFamily_succ_eq_runBlockPoint_last
    S hx hy i).trans
      (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
        (Fin.last (pathTwoOpenSubdivisionRunPredLength S i + 1)))

/-- The cumulative-prefix presentation of one run, rebased to the shared
global run-boundary family. -/
noncomputable def torusRP2_subdivisionRunGlobalPrefixBlockPath
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) : Path
      (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.castSucc :
        torusRP2PairingData.Space)
      (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy i.succ :
        torusRP2PairingData.Space) :=
  (Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
    (pathTwoOpenSubdivisionRunPrefixBlockPiece S i)).cast
      (torusRP2_subdivisionOuterRunBoundaryFamily_castSucc_eq_prefixBlockPoint_zero
        S hx hy i)
      (torusRP2_subdivisionOuterRunBoundaryFamily_succ_eq_prefixBlockPoint_last
        S hx hy i)

/-- The piecewise-cast original factors of a run have the class of its
globally rebased cumulative-prefix block. -/
theorem torusRP2_subdivisionRunGlobalPrefixBlockPath_class
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length) :
    Path.Homotopic.Quotient.cast
        (⟦Path.concat (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
          (fun k => (pathTwoOpenSubdivisionRunBlockPiece S i k).cast
            (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
              k.castSucc).symm
            (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
              k.succ).symm)⟧)
        (torusRP2_subdivisionOuterRunBoundaryFamily_castSucc_eq_prefixBlockPoint_zero
          S hx hy i)
        (torusRP2_subdivisionOuterRunBoundaryFamily_succ_eq_prefixBlockPoint_last
          S hx hy i) =
      ⟦torusRP2_subdivisionRunGlobalPrefixBlockPath S hx hy i⟧ := by
  exact congrArg
    (fun q => Path.Homotopic.Quotient.cast q
      (torusRP2_subdivisionOuterRunBoundaryFamily_castSucc_eq_prefixBlockPoint_zero
        S hx hy i)
      (torusRP2_subdivisionOuterRunBoundaryFamily_succ_eq_prefixBlockPoint_last
        S hx hy i))
    (torusRP2_subdivisionRunBlockConcat_cast_eq_prefixBlockConcat S i)

/-- Replacing every globally rebased run by its cumulative-prefix block
preserves the class of their ordered finite concatenation. -/
theorem torusRP2_subdivisionRunGlobalPrefixBlockConcat_class
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer) :
    (⟦Path.concat
        (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
          torusRP2PairingData.Space))
        (fun i => (Path.concat
          (pathTwoOpenSubdivisionRunPrefixBlockPoint S i)
          (fun k => (pathTwoOpenSubdivisionRunBlockPiece S i k).cast
            (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
              k.castSucc).symm
            (pathTwoOpenSubdivisionRunBlockPoint_eq_prefixBlockPoint S i
              k.succ).symm)).cast
                (torusRP2_subdivisionOuterRunBoundaryFamily_castSucc_eq_prefixBlockPoint_zero
                  S hx hy i)
                (torusRP2_subdivisionOuterRunBoundaryFamily_succ_eq_prefixBlockPoint_last
                  S hx hy i))⟧ : Path.Homotopic.Quotient _ _) =
      ⟦Path.concat
        (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
          torusRP2PairingData.Space))
        (torusRP2_subdivisionRunGlobalPrefixBlockPath S hx hy)⟧ := by
  exact torusRP2_pathHomotopicQuotient_concat_eq_of_pieceClass_eq
    (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
      torusRP2PairingData.Space)) _ _
    (fun i => torusRP2_subdivisionRunGlobalPrefixBlockPath_class S hx hy i)

/-- The global cumulative-prefix fold, rebased at the literal endpoints of
the original subordinate subdivision. -/
noncomputable def torusRP2_subdivisionGlobalPrefixBlockConcat_at_endpoints
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer) :
    Path (S.point 0) (S.point (Fin.last (S.n + 1))) :=
  (Path.concat
    (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
      torusRP2PairingData.Space))
    (torusRP2_subdivisionRunGlobalPrefixBlockPath S hx hy)).cast
      (torusRP2_subdivisionOuterRunBoundaryFamily_zero S hx hy).symm
      (torusRP2_subdivisionOuterRunBoundaryFamily_last S hx hy).symm

/-- The literal-endpoint prefix fold has exactly the quotient cast of the
global dependent concatenation. -/
theorem torusRP2_subdivisionGlobalPrefixBlockConcat_at_endpoints_class
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (hx : S.point 0 ∈ (openCover torusRP2PairingData).outer)
    (hy : S.point (Fin.last (S.n + 1)) ∈
      (openCover torusRP2PairingData).outer) :
    ⟦torusRP2_subdivisionGlobalPrefixBlockConcat_at_endpoints S hx hy⟧ =
      Path.Homotopic.Quotient.cast
        (⟦Path.concat
          (fun k => (pathTwoOpenSubdivisionOuterRunBoundaryFamily S hx hy k :
            torusRP2PairingData.Space))
          (torusRP2_subdivisionRunGlobalPrefixBlockPath S hx hy)⟧)
        (torusRP2_subdivisionOuterRunBoundaryFamily_zero S hx hy).symm
        (torusRP2_subdivisionOuterRunBoundaryFamily_last S hx hy).symm :=
  rfl

/-- A factor in the cumulative-prefix block for run `i` is literally the
original subdivision factor at the flattened index `prefixLength i + k`.
This is the pointwise identification used to compare the nested run fold
with the original subdivision fold. -/
theorem torusRP2_subdivisionRunPrefixBlockPiece_apply_globalIndex
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length)
    (k : Fin (pathTwoOpenSubdivisionRunPredLength S i + 1))
    (t : unitInterval) :
    pathTwoOpenSubdivisionRunPrefixBlockPiece S i k t =
      S.piece ⟨pathTwoOpenSubdivisionRunPrefixLength S i.val + k, by
        have h := pathTwoOpenSubdivisionRunPrefixBlock_le S i
        omega⟩ t := by
  rfl

/-- The flattened index of a factor in run `i` lies strictly before the
cumulative boundary of the next run. -/
theorem torusRP2_subdivisionRunPrefixBlockPiece_globalIndex_lt_next
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer)
    (i : Fin (boolSideRunPartition S.side).length)
    (k : Fin (pathTwoOpenSubdivisionRunPredLength S i + 1)) :
    pathTwoOpenSubdivisionRunPrefixLength S i.val + k <
      pathTwoOpenSubdivisionRunPrefixLength S (i.val + 1) := by
  rw [← pathTwoOpenSubdivisionRunPrefixLength_add_predLength S i]
  omega

/-- Cumulative run boundaries are strictly ordered.  Thus a flattened
subdivision factor can belong to at most one half-open run interval. -/
theorem torusRP2_subdivisionRunPrefixLength_strictMono
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer) :
    StrictMono (fun i : Fin ((boolSideRunPartition S.side).length + 1) =>
      pathTwoOpenSubdivisionRunPrefixLength S i.val) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  change pathTwoOpenSubdivisionRunPrefixLength S i.val <
    pathTwoOpenSubdivisionRunPrefixLength S (i.val + 1)
  rw [pathTwoOpenSubdivisionRunPrefixLength_succ S i.val (by omega)]
  exact Nat.lt_add_of_pos_right
    (pathTwoOpenSubdivisionRunFamily_length_pos S
      ⟨i.val, by omega⟩)

/-- The cumulative boundary family starts at zero and ends after every
subdivision factor. -/
theorem torusRP2_subdivisionRunPrefixLength_endpoints
    {x y : torusRP2PairingData.Space} {p : Path x y}
    (S : ConstructionTargets.FundamentalGroupoidOpenCoverSubdivision.PathTwoOpenSubdivision
      p (openCover torusRP2PairingData).inner
        (openCover torusRP2PairingData).outer) :
    pathTwoOpenSubdivisionRunPrefixLength S 0 = 0 ∧
      pathTwoOpenSubdivisionRunPrefixLength S
        (boolSideRunPartition S.side).length = S.n + 1 := by
  constructor
  · rfl
  · exact pathTwoOpenSubdivisionRunPrefixLength_all S

/-- Exact two-part output still required from the attaching-cell van Kampen
argument.  It is stated directly for the canonical free-group map so no
unproved injectivity of an intermediate coordinate map is hidden. -/
structure TorusRP2PairingSpaceBasedVanKampen : Prop where
  surjective : Function.Surjective torusRP2BoundaryFreeGroupMap
  ker_eq_relator :
    MonoidHom.ker torusRP2BoundaryFreeGroupMap =
      Subgroup.normalClosure ({torusRP2FrozenRelator} : Set (FreeGroup (Fin 3)))

/-- Algebraic assembly of the presentation once the exact based van Kampen
output is available. -/
noncomputable def torusRP2PairingSpace_fundamentalGroup_of_basedVanKampen
    (hvk : TorusRP2PairingSpaceBasedVanKampen) :
    FundamentalGroup torusRP2PairingData.Space
        (torusRP2SkeletonToPairingSpace torusRP2SkeletonBase) ≃*
      PresentedGroup ({torusRP2FrozenRelator} : Set (FreeGroup (Fin 3))) :=
  (QuotientGroup.quotientKerEquivOfSurjective
      torusRP2BoundaryFreeGroupMap hvk.surjective).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hvk.ker_eq_relator)

noncomputable instance torusRP2PairingSpace_pathConnectedSpace :
    PathConnectedSpace torusRP2PairingData.Space := by
  letI : PathConnectedSpace ConstructionTargets.Surfaces.Disk :=
    isPathConnected_iff_pathConnectedSpace.mp
      (Metric.isPathConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1))
  exact torusRP2PairingData.surjective_quotientMap.pathConnectedSpace
    torusRP2PairingData.continuous_quotientMap

/-- Move the based van Kampen presentation from the skeleton image to the
distinguished polygon centre used by the frozen theorem. -/
noncomputable def torusRP2PairingSpace_center_fundamentalGroup_of_basedVanKampen
    (hvk : TorusRP2PairingSpaceBasedVanKampen) :
    FundamentalGroup torusRP2PairingData.Space torusRP2PairingData.center ≃*
      PresentedGroup ({torusRP2FrozenRelator} : Set (FreeGroup (Fin 3))) :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected
      torusRP2PairingData.center
      (torusRP2SkeletonToPairingSpace torusRP2SkeletonBase)).trans
    (torusRP2PairingSpace_fundamentalGroup_of_basedVanKampen hvk)

#print axioms quotientLinearEquivOfMapEq
#print axioms fundamentalGroupEquivOfHomeomorph
#print axioms aabbccBoundaryCokernelSmithEquiv
#print axioms torusRP2BoundaryCokernelSmithEquiv
#print axioms torusRP2SkeletonFreeGroupMap_surjective
#print axioms torusRP2SkeletonFinFreeGroupMap_surjective
#print axioms torusRP2GeneratorSignHom_involutive
#print axioms torusRP2FrozenSkeletonFreeGroupMap_surjective
#print axioms torusRP2GeneratorSignHom_frozenRelator
#print axioms torusRP2PolygonBoundaryLegWord_coordinates
#print axioms torusRP2GeometricBoundary_eq_signedEdgeProduct
#print axioms polygonBoundaryExplicitEdgeClass_eq_zpow
#print axioms torusRP2SignedEdgeProduct_explicit
#print axioms torusRP2PositiveBoundaryBasisHom_relator
#print axioms torusRP2NegativeBoundaryBasisHom_relator
#print axioms normalClosure_singleton_conj
#print axioms torusRP2PositiveBoundary_normalClosure
#print axioms torusRP2NegativeBoundary_normalClosure
#print axioms torusRP2SkeletonFinFreeGroupMap_of
#print axioms torusRP2SkeletonFinFreeGroupMap_positiveBoundary
#print axioms torusRP2SkeletonFinFreeGroupMap_negativeBoundary
#print axioms torusRP2AttachingWord
#print axioms torusRP2DiskBoundaryPath_map_quotient_eq_one
#print axioms torusRP2DiskBoundaryBase_eq_skeletonBase
#print axioms torusRP2SkeletonBoundary_map_eq_diskBoundary_map
#print axioms torusRP2Relator_normalClosure_le_kernel
#print axioms torusRP2BoundaryFreeGroupMap_surjective
#print axioms torusRP2PolygonPseudopushout_arrow_eq_reconstructed
#print axioms torusRP2PolygonInner_pathClass_eq
#print axioms torusRP2PolygonInner_ambientPathClass_eq_outerOverlapReplacement
#print axioms torusRP2PolygonInnerRun_exists_outerOverlapReplacement
#print axioms torusRP2PolygonInnerBlock_exists_outerOverlapReplacement
#print axioms torusRP2_subdivision_quotient_eq_concat_of_pieceClass_eq
#print axioms torusRP2_subdivision_runPartition_boundary_spec
#print axioms torusRP2_subdivisionRun_exists_outerRepresentative
#print axioms torusRP2_subdivisionRun_exists_outerBoundaryPath
#print axioms torusRP2_subdivisionRunFold_exists_outerPath
#print axioms torusRP2_subdivisionRunFold_exists_outerPath_at_endpoints
#print axioms torusRP2_subdivisionRunBlockPiece_cast_eq_prefixBlockPiece
#print axioms torusRP2_subdivisionRunBlockConcat_cast_eq_prefixBlockConcat
#print axioms torusRP2_subdivisionRunPrefixBlock_adjacent
#print axioms torusRP2_subdivisionRunPrefixBlock_trans
#print axioms torusRP2_subdivisionRunPrefixBlockPoint_last
#print axioms torusRP2_subdivisionRunPrefixBlockPoint_zero
#print axioms torusRP2_subdivisionOuterRunBoundaryFamily_castSucc_eq_prefixBlockPoint_zero
#print axioms torusRP2_subdivisionOuterRunBoundaryFamily_succ_eq_prefixBlockPoint_last
#print axioms torusRP2_subdivisionRunGlobalPrefixBlockPath_class
#print axioms torusRP2_subdivisionRunGlobalPrefixBlockConcat_class
#print axioms torusRP2_subdivisionGlobalPrefixBlockConcat_at_endpoints_class
#print axioms torusRP2_subdivisionRunPrefixBlockPiece_apply_globalIndex
#print axioms torusRP2_subdivisionRunPrefixBlockPiece_globalIndex_lt_next
#print axioms torusRP2_subdivisionRunPrefixLength_strictMono
#print axioms torusRP2_subdivisionRunPrefixLength_endpoints
#print axioms torusRP2PairingSpace_fundamentalGroup_of_basedVanKampen
#print axioms torusRP2PairingSpace_center_fundamentalGroup_of_basedVanKampen

end ConstructionTargets.t97A01Closure
