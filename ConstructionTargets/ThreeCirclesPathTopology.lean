import ConstructionTargets.PointWedgePathConnected
import ConstructionTargets.T99J01PathComponentCoverRestriction
import ConstructionTargets.CircleHomology
import Mathlib.Geometry.Manifold.Instances.Sphere

open Set Topology

noncomputable section

namespace ConstructionTargets.ThreeCirclesPathTopology

open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.CoveringDegree
open ConstructionTargets.RestrictPathComponent
open ConstructionTargets.PointWedgeQuotient

private noncomputable instance sphereOneLocPathConnectedSpace :
    LocPathConnectedSpace (ConstructionTargets.SphereHomology.Sphere 1) :=
  ChartedSpace.locPathConnectedSpace (EuclideanSpace ℝ (Fin 1))
    (ConstructionTargets.SphereHomology.Sphere 1)

private noncomputable instance circleLocPathConnectedSpace :
    LocPathConnectedSpace Circle :=
  Topology.IsQuotientMap.locPathConnectedSpace
    ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.symm.isQuotientMap

private noncomputable instance circlePathConnectedSpace :
    PathConnectedSpace Circle :=
  pathConnectedSpace_iff_univ.mpr (by
    have h : IsPathConnected
        (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
          (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
      ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
        isPathConnected_univ
    simpa using h)

private noncomputable instance twoCirclesPathConnectedSpace :
    PathConnectedSpace TwoCircles := inferInstance

private noncomputable instance twoCirclesLocPathConnectedSpace :
    LocPathConnectedSpace TwoCircles :=
  Topology.IsQuotientMap.locPathConnectedSpace
    (show IsQuotientMap (quotientMap (1 : Circle) (1 : Circle)) from
      ⟨surjective_quotientMap _ _, rfl⟩)

noncomputable instance threeCirclesLocPathConnectedSpace :
    LocPathConnectedSpace ThreeCircles :=
  Topology.IsQuotientMap.locPathConnectedSpace
    (show IsQuotientMap (quotientMap twoCirclesPoint (1 : Circle)) from
      ⟨surjective_quotientMap _ _, rfl⟩)

noncomputable instance threeCirclesPathConnectedSpace :
    PathConnectedSpace ThreeCircles := inferInstance

/-- The topology instances above are exactly those needed to restrict a
finite-sheeted cover to the path component of a chosen point. -/
theorem restrictPathComponent_threeCircles
    {E : Type} [TopologicalSpace E] {n : ℕ} {p : E → ThreeCircles}
    (hp : IsKSheetedCover p n) (e : E) :
    IsCoveringMap
        (fun z : ConstructionTargets.CoveringPathComponentDomain.Component e ↦ p z.1) ∧
      Function.Surjective
        (fun z : ConstructionTargets.CoveringPathComponentDomain.Component e ↦ p z.1) := by
  exact hp.isCoveringMap.restrictPathComponent e

#print axioms threeCirclesLocPathConnectedSpace
#print axioms threeCirclesPathConnectedSpace
#print axioms restrictPathComponent_threeCircles

end ConstructionTargets.ThreeCirclesPathTopology
