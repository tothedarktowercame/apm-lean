import Mathlib
import ConstructionTargets.StatementSurfaceModels
import ConstructionTargets.RationalLefschetz

/-! # APM t99A03: fixed points on a wedge and a connected sum

This repairs the former generic deck-transformation stand-in by stating both
answers for concrete models of the spaces in the problem.
-/

open ConstructionTargets.PointWedgeQuotient
open ConstructionTargets.StatementSurfaceModels
open ConstructionTargets.Surfaces

noncomputable section

namespace T99A03

/-- The common point in the wedge of two projective planes. -/
def twoWedgePoint : ProjectivePlaneWedge :=
  quotientMap (surfacePoint false 1) (surfacePoint false 1)
    (Sum.inl (surfacePoint false 1))

/-- Four copies of `ℝP²`, joined at one point. -/
abbrev FourProjectivePlanesWedge := Wedge twoWedgePoint twoWedgePoint

/-- The connected sum of four copies of `ℝP²`. -/
abbrev FourProjectivePlanesConnectedSum := Surface false 4

end T99A03

theorem apm_t99a03 :
    (∀ f : C(T99A03.FourProjectivePlanesWedge,
        T99A03.FourProjectivePlanesWedge), ∃ x, f x = x) ∧
    (∃ f : C(T99A03.FourProjectivePlanesConnectedSum,
        T99A03.FourProjectivePlanesConnectedSum), ∀ x, f x ≠ x) := by
  sorry
