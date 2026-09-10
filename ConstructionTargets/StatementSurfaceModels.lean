import Mathlib
import ConstructionTargets.Surfaces
import ConstructionTargets.PointWedgeQuotient

/-! Concrete space and presentation vocabulary for the missing APM statements.
No classification or fixed-point theorem is assumed in these definitions.
The closed-disk polygon quotients use the existing coinduced topology. -/

noncomputable section
namespace ConstructionTargets.StatementSurfaceModels
open Surfaces PointWedgeQuotient

/-- The standard disk with boundary word `aa`, a concrete real projective plane. -/
abbrev RealProjectivePlane := Surface false 1

/-- The standard polygon with boundary word `aabb`, a concrete Klein bottle. -/
abbrev KleinBottle := Surface false 2

/-- The image of the center of the disk in its polygon quotient. -/
def surfacePoint (o : Bool) (g : ℕ) : Surface o g :=
  surfaceQuotient o g ⟨0, by simp [Disk, Metric.mem_closedBall]⟩

/-- Two projective planes with their chosen interior points identified. -/
abbrev ProjectivePlaneWedge := Wedge (surfacePoint false 1) (surfacePoint false 1)

abbrev TwoCircles := Wedge (1 : Circle) (1 : Circle)

def twoCirclesPoint : TwoCircles := quotientMap 1 1 (Sum.inl 1)

/-- Three circles identified at their basepoints, with the quotient topology. -/
abbrev ThreeCircles := Wedge twoCirclesPoint (1 : Circle)

/-- The product of the `g` commutators in the standard orientable surface word. -/
def surfaceRelator (g : ℕ) : FreeGroup (Fin g × Bool) :=
  (List.ofFn fun i : Fin g =>
    let a := FreeGroup.of (i, false)
    let b := FreeGroup.of (i, true)
    a * b * a⁻¹ * b⁻¹).prod

abbrev OrientableSurfaceGroup (g : ℕ) :=
  PresentedGroup ({surfaceRelator g} : Set (FreeGroup (Fin g × Bool)))

end ConstructionTargets.StatementSurfaceModels
