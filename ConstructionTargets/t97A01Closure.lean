import ConstructionTargets.PolygonSurfaceHomology
import ConstructionTargets.T97A01SmithQuotients

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
#print axioms torusRP2PairingSpace_fundamentalGroup_of_basedVanKampen
#print axioms torusRP2PairingSpace_center_fundamentalGroup_of_basedVanKampen

end ConstructionTargets.t97A01Closure
