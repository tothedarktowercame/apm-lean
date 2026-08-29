import ConstructionTargets.SolidTorusGluingOpenCover
import ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Fundamental-groupoid open cover for the two-solid-torus gluing

This file instantiates the generic two-open pseudopushout theorem on the
collared quotient cover and records the fundamental-groupoid equivalences
induced by the three compiled deformation equivalences.
-/

open Set CategoryTheory
open scoped ContinuousMap FundamentalGroupoid

noncomputable section

namespace ConstructionTargets.TwiceSpiralFundamentalGroupoidOpenCover

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout

variable (h : BoundaryTorus ≃ₜ BoundaryTorus)

/-- The left member of the collared cover of the gluing quotient. -/
abbrev U : Set (Gluing h) := leftOpen h

/-- The right member of the collared cover of the gluing quotient. -/
abbrev V : Set (Gluing h) := rightOpen h

theorem U_isOpen : IsOpen (U h) := leftOpen_isOpen h

theorem V_isOpen : IsOpen (V h) := rightOpen_isOpen h

theorem U_union_V : U h ∪ V h = Set.univ := leftOpen_union_rightOpen h

/-- The generic two-open fundamental-groupoid pseudopushout theorem,
specialized to the actual collared cover of `Gluing h`. -/
def gluingFundamentalGroupoidPseudopushoutEquivalence
    (C : Type) [Category C] :
    (FundamentalGroupoid (Gluing h) ⥤ C) ≌
      ConstructionTargets.TwoOpenFundamentalGroupoidSpan.PseudoFunctorCocone
        (X := Gluing h) (U := U h) (V := V h) (C := C) :=
  twoOpenFundamentalGroupoidPseudopushoutEquivalence
    (C := C) (U_isOpen h) (V_isOpen h) (U_union_V h)

/-- The left collared quotient piece has the fundamental groupoid of a solid
torus. -/
def leftFundamentalGroupoidEquivalence :
    FundamentalGroupoid (U h) ≌ FundamentalGroupoid SolidTorus :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (leftPieceHomotopyEquiv h)

/-- The right collared quotient piece has the fundamental groupoid of a solid
torus. -/
def rightFundamentalGroupoidEquivalence :
    FundamentalGroupoid (V h) ≌ FundamentalGroupoid SolidTorus :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (rightPieceHomotopyEquiv h)

/-- The overlap of the collared quotient pieces has the fundamental groupoid
of the boundary torus. -/
def overlapFundamentalGroupoidEquivalence :
    FundamentalGroupoid (U h ∩ V h : Set (Gluing h)) ≌
      FundamentalGroupoid BoundaryTorus :=
  FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (intersectionPieceHomotopyEquiv h)

/-- In the compiled deformation coordinates, the overlap-to-left inclusion
is the literal boundary inclusion on fundamental groupoids. -/
theorem overlapToLeft_groupoid_coordinate :
    FundamentalGroupoid.map (intersectionPieceHomotopyEquiv h).invFun ⋙
        FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
        FundamentalGroupoid.map (leftPieceHomotopyEquiv h).toFun =
      FundamentalGroupoid.map
        ⟨boundaryInclusion, continuous_boundaryInclusion⟩ := by
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  exact congrArg FundamentalGroupoid.map (intersection_left_coordinate_strict h)

/-- In the compiled deformation coordinates, the overlap-to-right inclusion
is boundary inclusion after the gluing homeomorphism. -/
theorem overlapToRight_groupoid_coordinate :
    FundamentalGroupoid.map (intersectionPieceHomotopyEquiv h).invFun ⋙
        FundamentalGroupoid.map (intersectionToRightOpen h) ⋙
        FundamentalGroupoid.map (rightPieceHomotopyEquiv h).toFun =
      FundamentalGroupoid.map
        ⟨boundaryInclusion ∘ h,
          continuous_boundaryInclusion.comp h.continuous⟩ := by
  rw [← FundamentalGroupoid.map_comp, ← FundamentalGroupoid.map_comp]
  exact congrArg FundamentalGroupoid.map (intersection_right_coordinate_strict h)

#print axioms U_isOpen
#print axioms V_isOpen
#print axioms U_union_V
#print axioms gluingFundamentalGroupoidPseudopushoutEquivalence
#print axioms leftFundamentalGroupoidEquivalence
#print axioms rightFundamentalGroupoidEquivalence
#print axioms overlapFundamentalGroupoidEquivalence
#print axioms overlapToLeft_groupoid_coordinate
#print axioms overlapToRight_groupoid_coordinate

end ConstructionTargets.TwiceSpiralFundamentalGroupoidOpenCover
