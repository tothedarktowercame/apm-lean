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

end ConstructionTargets.t97A01Closure
