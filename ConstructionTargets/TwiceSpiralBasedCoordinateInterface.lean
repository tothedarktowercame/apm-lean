import ConstructionTargets.TwiceSpiralH1Coordinates
import ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

/-!
# Based coordinate interface for the twice-spiral span

This target packages the frozen twice-spiral coordinate hypotheses into the
based automorphism-group interface used downstream of the groupoid
pseudopushout.  The right solid-torus basepoint remains
`boundaryInclusion (h z₀)`.
-/

open CategoryTheory
open scoped ContinuousMap FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralBasedCoordinateInterface

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralH1Coordinates
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

/-- The actual frozen coordinate hypotheses supply the based coordinate
interface, with `d` defined as the second coefficient of the boundary
homeomorphism. -/
def ofCoordinateHypotheses
    (h : BoundaryTorus ≃ₜ BoundaryTorus) (z₀ : BoundaryTorus)
    (e₁ : FundamentalGroup BoundaryTorus z₀ ≃* Multiplicative (ℤ × ℤ))
    (e₂ : FundamentalGroup BoundaryTorus (h z₀) ≃* Multiplicative (ℤ × ℤ))
    (c₁ : FundamentalGroup SolidTorus (boundaryInclusion z₀) ≃*
      Multiplicative ℤ)
    (c₂ : FundamentalGroup SolidTorus (boundaryInclusion (h z₀)) ≃*
      Multiplicative ℤ)
    (hinc₁ : ∀ g, c₁ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ z₀ g) =
        Multiplicative.ofAdd (e₁ g).toAdd.2)
    (hinc₂ : ∀ g, c₂ (FundamentalGroup.map
      ⟨boundaryInclusion, continuous_boundaryInclusion⟩ (h z₀) g) =
        Multiplicative.ofAdd (e₂ g).toAdd.2)
    (h10 : boundaryCoordinateMap h z₀ e₁ e₂
      (Multiplicative.ofAdd (1, 0)) = Multiplicative.ofAdd (1, 2)) :
    BasedTwiceSpiralCoordinateInterface h
      (twiceSpiralSecondCoefficient h z₀ e₁ e₂) where
  boundaryBase := z₀
  boundaryCoord := e₁
  leftCoord := c₁
  rightCoord := c₂
  left_leg := hinc₁
  right_leg := by
    intro g
    rw [show FundamentalGroup.map
        ⟨boundaryInclusion ∘ h,
          continuous_boundaryInclusion.comp h.continuous⟩ z₀ g =
      FundamentalGroup.map ⟨boundaryInclusion,
          continuous_boundaryInclusion⟩ (h z₀)
        (FundamentalGroup.map ⟨h, h.continuous⟩ z₀ g) by
      rcases g with ⟨p⟩
      rfl]
    rw [hinc₂]
    have hb : e₂ (FundamentalGroup.map ⟨h, h.continuous⟩ z₀ g) =
        boundaryCoordinateMap h z₀ e₁ e₂ (e₁ g) := by
      simp [boundaryCoordinateMap]
    rw [hb]
    exact congrArg Multiplicative.ofAdd (by
      simpa using boundaryCoordinateMap_second_formula h z₀ e₁ e₂ h10
        (e₁ g).toAdd.1 (e₁ g).toAdd.2)

#print axioms ofCoordinateHypotheses

end ConstructionTargets.TwiceSpiralBasedCoordinateInterface
