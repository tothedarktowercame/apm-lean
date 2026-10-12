import ConstructionTargets.KleinPlaneAffineAction

/-!
# Freeness of the affine Klein-bottle action

The explicit action of the presented Klein group on the plane is free.  This
is the freeness hypothesis needed by the general deck-group computation of
the fundamental group of an orbit quotient.
-/

namespace KleinPlaneAffineAction

open KleinPresentedGroupCoordinateModel
open KleinPresentedGroupCoordinateNormalForm

theorem eq_one_of_smul_eq (g : PresentedKleinGroup) (p : ℝ × ℝ)
    (h : g • p = p) : g = 1 := by
  let c := coordinateEquiv g
  have hc : coordinateAct c p = p := by
    simpa [c, planeAction] using h
  have hy := congrArg Prod.snd hc
  have hnR : ((Multiplicative.toAdd c.2 : ℤ) : ℝ) = 0 := by
    dsimp [coordinateAct] at hy
    linarith
  have hn : Multiplicative.toAdd c.2 = 0 := by
    exact_mod_cast hnR
  have hc2 : c.2 = 1 := by
    apply Multiplicative.toAdd.injective
    simpa using hn
  have hx := congrArg Prod.fst hc
  have hc1 : c.1 = 1 := by
    dsimp [coordinateAct] at hx
    simpa [hc2] using hx
  apply coordinateEquiv.injective
  change c = coordinateEquiv 1
  rw [map_one]
  apply SemidirectProduct.ext
  · exact hc1
  · exact hc2

end KleinPlaneAffineAction
