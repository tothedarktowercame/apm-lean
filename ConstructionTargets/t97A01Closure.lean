import ConstructionTargets.PolygonSurfaceHomology

/-!
# Closure adapters for t97A01

This module specializes the general polygon-surface homology theorem to the
two six-edge pairing records occurring in the frozen problem.  Later closure
steps identify these quotient spaces with the literal `EqvGen` quotients and
reduce the displayed kernel and cokernel models to the requested groups.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.t97A01Closure

open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfaceHomology

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

end ConstructionTargets.t97A01Closure
