import ConstructionTargets.PolygonSurfaceHomology
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Data.ZMod.Basic

/-! Compiled closure infrastructure for t94J09. -/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace ConstructionTargets.t94J09Closure

open ConstructionTargets.PolygonSurfacePiOne
open ConstructionTargets.PolygonSurfaceHomology

/-- The standard one-vertex twelve-gon for the nonorientable genus-six
surface. -/
def n6PairingData : PairingData :=
  nonorientableStandardPairingData 6 (by omega)

theorem n6PolygonHomology :
    Nonempty (H n6PairingData 0 ≅ ModuleCat.of ℤ ℤ) ∧
      Nonempty (H n6PairingData 1 ≅
        ModuleCat.of ℤ (BoundaryCokernel n6PairingData)) ∧
      Nonempty (H n6PairingData 2 ≅
        ModuleCat.of ℤ (BoundaryKernel n6PairingData)) ∧
      ∀ k : ℕ, 3 ≤ k → IsZero (H n6PairingData k) :=
  polygonQuotient_homology n6PairingData

/-- The six standard edge-orbit coordinates. -/
def n6OrbitCoordinates :
    (PairingOrbit n6PairingData.pair → ℤ) ≃ₗ[ℤ] (Fin 6 → ℤ) :=
  { toFun := fun f j => f ((nonorientableOrbitEquiv 6).symm j)
    invFun := fun v q => v (nonorientableOrbitEquiv 6 q)
    left_inv := by intro f; funext q; simp
    right_inv := by intro v; funext j; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }

@[simp] theorem n6OrbitEquiv_orbit (i : Fin 12) :
    nonorientableOrbitEquiv 6 (n6PairingData.orbit i) =
      nonorientableOrbitLabel 6 i := rfl

@[simp] theorem n6_orbit_eq_named (i : Fin 12) (j : Fin 6) :
    n6PairingData.orbit i = (nonorientableOrbitEquiv 6).symm j ↔
      nonorientableOrbitEquiv 6 (n6PairingData.orbit i) = j :=
  (nonorientableOrbitEquiv 6).eq_symm_apply

theorem n6_attachingDegree_named (j : Fin 6) :
    attachingDegree n6PairingData ((nonorientableOrbitEquiv 6).symm j) = -2 := by
  rw [attachingDegree_apply]
  simp_rw [edgeOrbitContribution, n6_orbit_eq_named]
  simp_rw [n6OrbitEquiv_orbit]
  fin_cases j <;>
    simp [n6PairingData, nonorientableStandardPairingData,
      standardPairingDataOfOneVertex, standardPair, standardSign,
      nonorientableOrbitLabel, nonorientableCoord, edgeAttachingDegree] <;>
      decide

theorem n6OrbitCoordinates_attachingDegree :
    n6OrbitCoordinates (attachingDegree n6PairingData) = fun _ => -2 := by
  funext j
  exact n6_attachingDegree_named j

/-- Smith-normal boundary vector for the standard genus-six polygon. -/
def n6BoundaryLinear : ℤ →ₗ[ℤ] (Fin 6 → ℤ) where
  toFun n := fun _ => 2 * n
  map_add' := by intros; funext; simp [mul_add]
  map_smul' := by intros; funext; simp [mul_left_comm]

theorem n6OrbitCoordinates_comp_attachingBoundary :
    n6OrbitCoordinates.toLinearMap.comp (attachingBoundary n6PairingData) =
      -n6BoundaryLinear := by
  apply LinearMap.ext
  intro n
  funext j
  change n * attachingDegree n6PairingData
      ((nonorientableOrbitEquiv 6).symm j) = _
  rw [n6_attachingDegree_named]
  simp [n6BoundaryLinear]
  ring

theorem n6BoundaryLinear_injective : Function.Injective n6BoundaryLinear := by
  intro a b h
  have h0 := congrFun h (0 : Fin 6)
  dsimp [n6BoundaryLinear] at h0
  omega

theorem n6AttachingBoundary_injective :
    Function.Injective (attachingBoundary n6PairingData) := by
  intro a b h
  apply n6BoundaryLinear_injective
  have hc := congrArg n6OrbitCoordinates h
  have ha := LinearMap.congr_fun n6OrbitCoordinates_comp_attachingBoundary a
  have hb := LinearMap.congr_fun n6OrbitCoordinates_comp_attachingBoundary b
  simpa [LinearMap.comp_apply] using ha.symm.trans (hc.trans hb)

theorem n6BoundaryKernel_eq_bot : BoundaryKernel n6PairingData = ⊥ :=
  LinearMap.ker_eq_bot.mpr n6AttachingBoundary_injective

#print axioms n6PolygonHomology
#print axioms n6AttachingBoundary_injective
#print axioms n6BoundaryKernel_eq_bot

end ConstructionTargets.t94J09Closure
