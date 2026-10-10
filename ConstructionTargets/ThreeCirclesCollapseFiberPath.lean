import ConstructionTargets.CyclicThreeCirclesCollapse
import ConstructionTargets.PointWedgePathConnected
import ConstructionTargets.CircleHomology

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels

noncomputable section

namespace ConstructionTargets.ThreeCirclesCollapseFiberPath

open ConstructionTargets.CyclicThreeCirclesCollapse
open ConstructionTargets.PointWedgePathConnected

/-- Every point of `ThreeCircles` can be moved to the final-circle section
without changing its value under `collapse`. -/
theorem exists_collapseFiber_path (y : ThreeCircles) :
    ∃ γ : Path y (firstCircle (collapse y)),
      ∀ t, collapse (γ t) = collapse y := by
  letI : PathConnectedSpace Circle :=
    pathConnectedSpace_iff_univ.mpr (by
      have h : IsPathConnected
          (ConstructionTargets.CircleHomology.circleHomeomorphSphereOne ⁻¹'
            (Set.univ : Set (ConstructionTargets.SphereHomology.Sphere 1))) :=
        ConstructionTargets.CircleHomology.circleHomeomorphSphereOne.isPathConnected_preimage.mpr
          isPathConnected_univ
      simpa using h)
  letI : PathConnectedSpace TwoCircles :=
    wedgePathConnectedSpace (1 : Circle) (1 : Circle)
  refine Quotient.inductionOn y ?_
  intro s
  cases s with
  | inl x =>
      obtain ⟨δ⟩ := PathConnectedSpace.joined x twoCirclesPoint
      let hleft : Continuous (fun x : TwoCircles =>
          quotientMap twoCirclesPoint (1 : Circle) (.inl x)) :=
        (continuous_quotientMap twoCirclesPoint (1 : Circle)).comp continuous_inl
      let γ₀ := δ.map hleft
      let γ : Path
          (quotientMap twoCirclesPoint (1 : Circle) (.inl x))
          (firstCircle (collapse
            (quotientMap twoCirclesPoint (1 : Circle) (.inl x)))) :=
        γ₀.cast rfl (wedgePoint_eq twoCirclesPoint (1 : Circle)).symm
      refine ⟨γ, ?_⟩
      intro t
      rfl
  | inr z =>
      refine ⟨Path.refl (firstCircle z), ?_⟩
      intro t
      rfl

#print axioms exists_collapseFiber_path

end ConstructionTargets.ThreeCirclesCollapseFiberPath
