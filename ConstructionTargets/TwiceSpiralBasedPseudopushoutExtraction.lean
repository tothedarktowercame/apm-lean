import ConstructionTargets.TwiceSpiralPseudococoneTransport
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# Based extraction from the twice-spiral coordinate pseudopushout

This file evaluates a coordinate pseudococone at chosen base objects.  The
overlap natural isomorphism then says precisely that the two induced vertex
group homomorphisms agree after conjugation by its base component.
-/

open CategoryTheory
open scoped FundamentalGroupoid

noncomputable section

namespace ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
open ConstructionTargets.TwiceSpiralPseudococoneTransport

variable (h : BoundaryTorus ≃ₜ BoundaryTorus)
variable (C : Type) [Groupoid C]

/-- Coordinate data retained when passing from the groupoid mapping property
to vertex groups.  The two solid-torus base objects are determined, but remain
distinct: the right one contains the gluing homeomorphism. -/
structure PointedCoordinateBases (d : ℤ) where
  coordinates : BasedTwiceSpiralCoordinateInterface h d

namespace PointedCoordinateBases

variable {h C} {d : ℤ} (B : PointedCoordinateBases h d)

abbrev boundaryBase : BoundaryTorus := B.coordinates.boundaryBase

abbrev leftBase : SolidTorus := boundaryInclusion B.boundaryBase

abbrev rightBase : SolidTorus := boundaryInclusion (h B.boundaryBase)

/-- The actual overlap component identifying the two target base objects. -/
def glueBaseIso (Q : CoordinatePseudoCocone h C) :
    Q.left.obj (FundamentalGroupoid.mk B.leftBase) ≅
      Q.right.obj (FundamentalGroupoid.mk B.rightBase) :=
  Q.glue.app (FundamentalGroupoid.mk B.boundaryBase)

/-- Left vertex-group representation extracted from a coordinate
pseudococone. -/
def leftAutomorphismHom (Q : CoordinatePseudoCocone h C) :
    FundamentalGroup SolidTorus B.leftBase →*
      End (Q.left.obj (FundamentalGroupoid.mk B.leftBase)) :=
  Q.left.mapEnd _

/-- Right vertex-group representation extracted from a coordinate
pseudococone. -/
def rightAutomorphismHom (Q : CoordinatePseudoCocone h C) :
    FundamentalGroup SolidTorus B.rightBase →*
      End (Q.right.obj (FundamentalGroupoid.mk B.rightBase)) :=
  Q.right.mapEnd _

/-- Boundary automorphisms restricted through the left coordinate leg. -/
def boundaryToLeftAutomorphismHom (Q : CoordinatePseudoCocone h C) :
    FundamentalGroup BoundaryTorus B.boundaryBase →*
      End (Q.left.obj (FundamentalGroupoid.mk B.leftBase)) :=
  Q.left.mapEnd _ |>.comp (coordinateLeftLeg.mapEnd _)

/-- Boundary automorphisms restricted through the right coordinate leg. -/
def boundaryToRightAutomorphismHom (Q : CoordinatePseudoCocone h C) :
    FundamentalGroup BoundaryTorus B.boundaryBase →*
      End (Q.right.obj (FundamentalGroupoid.mk B.rightBase)) :=
  Q.right.mapEnd _ |>.comp ((coordinateRightLeg h).mapEnd _)

/-- The two boundary restrictions agree after conjugation by the actual glue
component at the boundary base object. -/
theorem boundaryRestrictions_conjugate
    (Q : CoordinatePseudoCocone h C)
    (g : FundamentalGroup BoundaryTorus B.boundaryBase) :
    (B.glueBaseIso Q).conj (B.boundaryToLeftAutomorphismHom Q g) =
      B.boundaryToRightAutomorphismHom Q g := by
  dsimp [glueBaseIso, boundaryToLeftAutomorphismHom,
    boundaryToRightAutomorphismHom, Iso.conj_apply]
  apply (Q.glue.app (FundamentalGroupoid.mk B.boundaryBase)).inv_comp_eq.mpr
  exact Q.glue.hom.naturality g

/-- Homomorphism-level form of `boundaryRestrictions_conjugate`. -/
theorem boundaryRestrictions_conjugate_hom
    (Q : CoordinatePseudoCocone h C) :
    (B.glueBaseIso Q).conj.toMonoidHom.comp
        (B.boundaryToLeftAutomorphismHom Q) =
      B.boundaryToRightAutomorphismHom Q := by
  ext g
  exact B.boundaryRestrictions_conjugate Q g

end PointedCoordinateBases

#print axioms PointedCoordinateBases.glueBaseIso
#print axioms PointedCoordinateBases.leftAutomorphismHom
#print axioms PointedCoordinateBases.rightAutomorphismHom
#print axioms PointedCoordinateBases.boundaryToLeftAutomorphismHom
#print axioms PointedCoordinateBases.boundaryToRightAutomorphismHom
#print axioms PointedCoordinateBases.boundaryRestrictions_conjugate
#print axioms PointedCoordinateBases.boundaryRestrictions_conjugate_hom

end ConstructionTargets.TwiceSpiralBasedPseudopushoutExtraction
