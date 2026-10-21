import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.RationalLefschetz

/-! # Closure support for t99A03

This module copies the blueprint's proved concrete models and isolates the
covering-space adapter used after construction of the `N₄ → N₃` double cover.
-/

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.Surfaces

noncomputable section

namespace ConstructionTargets.t99A03Closure

def twoWedgePoint : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1)
    (Sum.inl (surfacePoint false 1))

abbrev FourProjectivePlanesWedge := Wedge twoWedgePoint twoWedgePoint
abbrev FourProjectivePlanesConnectedSum := Surface false 4
abbrev ThreeProjectivePlanesConnectedSum := Surface false 3

/-- A nonidentity deck transformation of a connected covering has no fixed
point, by uniqueness of lifts against the identity map. -/
theorem deckTransformation_fixedPointFree
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [ConnectedSpace E] (p : E → B) (hp : IsCoveringMap p)
    (τ : E ≃ₜ E) (hdeck : p ∘ τ = p)
    (hne : τ ≠ Homeomorph.refl E) : ∀ x : E, τ x ≠ x := by
  intro x hx
  apply hne
  have hfun : (τ : E → E) = id :=
    hp.eq_of_comp_eq τ.continuous continuous_id (by simpa using hdeck) x
      (by simpa using hx)
  exact Homeomorph.ext (fun y ↦ by simpa using congrFun hfun y)

/-- The exact adapter from the planned `N₄ → N₃` deck data to the
fixed-point-free self-map required by the registered theorem. -/
theorem exists_fixedPointFree_selfMap_of_deckData
    [ConnectedSpace FourProjectivePlanesConnectedSum]
    (p : FourProjectivePlanesConnectedSum →
      ThreeProjectivePlanesConnectedSum)
    (τ : FourProjectivePlanesConnectedSum ≃ₜ
      FourProjectivePlanesConnectedSum)
    (hp : IsCoveringMap p) (hdeck : p ∘ τ = p)
    (hne : τ ≠ Homeomorph.refl FourProjectivePlanesConnectedSum) :
    ∃ f : C(FourProjectivePlanesConnectedSum,
        FourProjectivePlanesConnectedSum), ∀ x, f x ≠ x :=
  ⟨τ, deckTransformation_fixedPointFree p hp τ hdeck hne⟩

#print axioms deckTransformation_fixedPointFree
#print axioms exists_fixedPointFree_selfMap_of_deckData

end ConstructionTargets.t99A03Closure
