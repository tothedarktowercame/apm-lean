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

end ConstructionTargets.t97A01Closure
