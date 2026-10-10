import ConstructionTargets.PolygonAnnulusRadialHomotopy

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonOverlapHomotopyEquivCircle

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonAnnularOverlapHomeomorph
open ConstructionTargets.PolygonAnnulusRadialMaps
open ConstructionTargets.PolygonAnnulusRadialHomotopy

variable (R : Surfaces.Disk → Surfaces.Disk → Prop)

/-- The actual quotient overlap has the circle homotopy model obtained by
transporting the literal annulus model through `overlapHomeomorph`. -/
def overlapHomotopyEquivCircle
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1) :
    ContinuousMap.HomotopyEquiv Circle (overlapOpen R) :=
  annulusHomotopyEquivCircle.trans
    (overlapHomeomorph R hR hboundary).toHomotopyEquiv

@[simp] theorem overlapHomotopyEquivCircle_apply
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (z : Circle) :
    overlapHomotopyEquivCircle R hR hboundary z =
      overlapMap R (halfCircleMap z) := by
  rfl

@[simp] theorem overlapHomotopyEquivCircle_symm_apply_overlapMap
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (x : Annulus) :
    (overlapHomotopyEquivCircle R hR hboundary).symm (overlapMap R x) =
      radialNormalizeMap x := by
  change radialNormalizeMap
      ((overlapHomeomorph R hR hboundary).symm (overlapMap R x)) = _
  rw [← overlapHomeomorph_apply R hR hboundary x]
  rw [Homeomorph.symm_apply_apply]

theorem overlapHomotopyEquivCircle_apply_val
    (hR : ∀ ⦃x y⦄, R x y → radius x = radius y)
    (hboundary : ∀ ⦃x y⦄, R x y → radius x = 1 ∧ radius y = 1)
    (z : Circle) :
    (overlapHomotopyEquivCircle R hR hboundary z).1 =
      quotientMap R (halfCircleMap z).1 := by
  rfl

end ConstructionTargets.PolygonOverlapHomotopyEquivCircle
