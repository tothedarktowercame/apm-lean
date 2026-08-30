import ConstructionTargets.TwiceSpiralFundamentalGroupoidOpenCover
import ConstructionTargets.TwiceSpiralFundamentalGroupPushout

/-!
# Coordinate pseudococones for the twice-spiral groupoid span

This target names the span after transporting its three groupoids to the
solid-torus/boundary-torus coordinates.  Its cocones retain an invertible
overlap 2-cell; they are not strict cocones.
-/

open CategoryTheory
open scoped ContinuousMap FundamentalGroupoid
noncomputable section

namespace ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates

open ConstructionTargets.SolidTorusGluingOpenCover
open ConstructionTargets.TwiceSpiralFundamentalGroupoidOpenCover

variable (h : BoundaryTorus ≃ₜ BoundaryTorus)
variable (C : Type) [Category C]

/-- The left leg of the coordinate groupoid span. -/
def coordinateLeftLeg :
    FundamentalGroupoid BoundaryTorus ⥤ FundamentalGroupoid SolidTorus :=
  FundamentalGroupoid.map ⟨boundaryInclusion, continuous_boundaryInclusion⟩

/-- The right leg of the coordinate groupoid span. -/
def coordinateRightLeg :
    FundamentalGroupoid BoundaryTorus ⥤ FundamentalGroupoid SolidTorus :=
  FundamentalGroupoid.map
    ⟨boundaryInclusion ∘ h, continuous_boundaryInclusion.comp h.continuous⟩

/-- A pseudococone over the coordinate span.  The two solid-torus functors
need only agree on the boundary-torus overlap up to the displayed natural
isomorphism. -/
structure CoordinatePseudoCocone where
  left : FundamentalGroupoid SolidTorus ⥤ C
  right : FundamentalGroupoid SolidTorus ⥤ C
  glue : coordinateLeftLeg ⋙ left ≅ coordinateRightLeg h ⋙ right

/-- Morphisms of coordinate pseudococones preserve the overlap 2-cell. -/
structure CoordinatePseudoCoconeHom (P Q : CoordinatePseudoCocone h C) where
  left : P.left ⟶ Q.left
  right : P.right ⟶ Q.right
  glue_naturality : P.glue.hom ≫ Functor.whiskerLeft (coordinateRightLeg h) right =
    Functor.whiskerLeft coordinateLeftLeg left ≫ Q.glue.hom

@[ext] theorem CoordinatePseudoCoconeHom.ext
    {P Q : CoordinatePseudoCocone h C}
    {f g : CoordinatePseudoCoconeHom h C P Q}
    (hl : f.left = g.left) (hr : f.right = g.right) : f = g := by
  cases f
  cases g
  simp_all

instance : Category (CoordinatePseudoCocone h C) where
  Hom := CoordinatePseudoCoconeHom h C
  id P := {
    left := 𝟙 P.left
    right := 𝟙 P.right
    glue_naturality := by simp }
  comp f g := {
    left := f.left ≫ g.left
    right := f.right ≫ g.right
    glue_naturality := by
      rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
      rw [← Category.assoc, f.glue_naturality]
      simp only [Category.assoc]
      rw [g.glue_naturality] }
  id_comp _ := by ext <;> simp
  comp_id _ := by ext <;> simp
  assoc _ _ _ := by ext <;> simp [Category.assoc]

section Postcomposition

variable {C D : Type} [Category C] [Category D]

/-- Postcompose both coordinate-piece functors and their invertible overlap
comparison by a target functor. -/
def postcomposeCoordinatePseudoCoconeObj
    (H : C ⥤ D) (P : CoordinatePseudoCocone h C) :
    CoordinatePseudoCocone h D where
  left := P.left ⋙ H
  right := P.right ⋙ H
  glue := Functor.isoWhiskerRight P.glue H

@[simp] theorem postcomposeCoordinatePseudoCoconeObj_left
    (H : C ⥤ D) (P : CoordinatePseudoCocone h C) :
    (postcomposeCoordinatePseudoCoconeObj h H P).left = P.left ⋙ H := rfl

@[simp] theorem postcomposeCoordinatePseudoCoconeObj_right
    (H : C ⥤ D) (P : CoordinatePseudoCocone h C) :
    (postcomposeCoordinatePseudoCoconeObj h H P).right = P.right ⋙ H := rfl

@[simp] theorem postcomposeCoordinatePseudoCoconeObj_glue
    (H : C ⥤ D) (P : CoordinatePseudoCocone h C) :
    (postcomposeCoordinatePseudoCoconeObj h H P).glue =
      Functor.isoWhiskerRight P.glue H := rfl

/-- Postcomposition sends a coordinate-pseudococone morphism componentwise;
the glue square is the image of the original componentwise square. -/
def postcomposeCoordinatePseudoCoconeMap
    (H : C ⥤ D) {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q) :
    postcomposeCoordinatePseudoCoconeObj h H P ⟶
      postcomposeCoordinatePseudoCoconeObj h H Q where
  left := Functor.whiskerRight τ.left H
  right := Functor.whiskerRight τ.right H
  glue_naturality := by
    ext z
    simpa [postcomposeCoordinatePseudoCoconeObj] using
      congrArg H.map (NatTrans.congr_app τ.glue_naturality z)

@[simp] theorem postcomposeCoordinatePseudoCoconeMap_left_app
    (H : C ⥤ D) {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (z : FundamentalGroupoid SolidTorus) :
    (postcomposeCoordinatePseudoCoconeMap h H τ).left.app z =
      H.map (τ.left.app z) := rfl

@[simp] theorem postcomposeCoordinatePseudoCoconeMap_right_app
    (H : C ⥤ D) {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (z : FundamentalGroupoid SolidTorus) :
    (postcomposeCoordinatePseudoCoconeMap h H τ).right.app z =
      H.map (τ.right.app z) := rfl

/-- Target postcomposition on the category of coordinate pseudococones. -/
def postcomposeCoordinatePseudoCoconeFunctor
    (H : C ⥤ D) : CoordinatePseudoCocone h C ⥤ CoordinatePseudoCocone h D where
  obj := postcomposeCoordinatePseudoCoconeObj h H
  map := postcomposeCoordinatePseudoCoconeMap h H
  map_id P := by
    apply CoordinatePseudoCoconeHom.ext <;> ext z
    · change H.map (𝟙 _) = 𝟙 _
      simp
    · change H.map (𝟙 _) = 𝟙 _
      simp
  map_comp f g := by
    apply CoordinatePseudoCoconeHom.ext <;> ext z
    · change H.map (f.left.app z ≫ g.left.app z) =
        H.map (f.left.app z) ≫ H.map (g.left.app z)
      simp
    · change H.map (f.right.app z ≫ g.right.app z) =
        H.map (f.right.app z) ≫ H.map (g.right.app z)
      simp

@[simp] theorem postcomposeCoordinatePseudoCoconeFunctor_obj_left
    (H : C ⥤ D) (P : CoordinatePseudoCocone h C) :
    ((postcomposeCoordinatePseudoCoconeFunctor h H).obj P).left = P.left ⋙ H := rfl

@[simp] theorem postcomposeCoordinatePseudoCoconeFunctor_obj_right
    (H : C ⥤ D) (P : CoordinatePseudoCocone h C) :
    ((postcomposeCoordinatePseudoCoconeFunctor h H).obj P).right = P.right ⋙ H := rfl

@[simp] theorem postcomposeCoordinatePseudoCoconeFunctor_map_left_app
    (H : C ⥤ D) {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (z : FundamentalGroupoid SolidTorus) :
    ((postcomposeCoordinatePseudoCoconeFunctor h H).map τ).left.app z =
      H.map (τ.left.app z) := rfl

@[simp] theorem postcomposeCoordinatePseudoCoconeFunctor_map_right_app
    (H : C ⥤ D) {P Q : CoordinatePseudoCocone h C} (τ : P ⟶ Q)
    (z : FundamentalGroupoid SolidTorus) :
    ((postcomposeCoordinatePseudoCoconeFunctor h H).map τ).right.app z =
      H.map (τ.right.app z) := rfl

end Postcomposition

/-- The actual overlap-to-left span leg becomes the coordinate left leg after
the compiled inverse-overlap/forward-piece transports. -/
theorem actual_left_leg_in_coordinates :
    FundamentalGroupoid.map (intersectionPieceHomotopyEquiv h).invFun ⋙
        FundamentalGroupoid.map (intersectionToLeftOpen h) ⋙
        FundamentalGroupoid.map (leftPieceHomotopyEquiv h).toFun =
      coordinateLeftLeg :=
  overlapToLeft_groupoid_coordinate h

/-- The actual overlap-to-right span leg becomes boundary inclusion after
`h`, with the same explicit equivalence orientation. -/
theorem actual_right_leg_in_coordinates :
    FundamentalGroupoid.map (intersectionPieceHomotopyEquiv h).invFun ⋙
        FundamentalGroupoid.map (intersectionToRightOpen h) ⋙
        FundamentalGroupoid.map (rightPieceHomotopyEquiv h).toFun =
      coordinateRightLeg h :=
  overlapToRight_groupoid_coordinate h

/-- Data still required to pass from the groupoid pseudopushout to the banked
one-object group pushout: a chosen object in each groupoid, compatible object
transports along both legs, and identification of the induced automorphism
homomorphisms with the twice-spiral boundary maps. -/
structure BasedTwiceSpiralCoordinateInterface (d : ℤ) where
  boundaryBase : BoundaryTorus
  boundaryCoord :
    FundamentalGroup BoundaryTorus boundaryBase ≃* Multiplicative (ℤ × ℤ)
  leftCoord : FundamentalGroup SolidTorus (boundaryInclusion boundaryBase) ≃*
    Multiplicative ℤ
  rightCoord : FundamentalGroup SolidTorus
      (boundaryInclusion (h boundaryBase)) ≃* Multiplicative ℤ
  left_leg : ∀ g,
    leftCoord (FundamentalGroup.map ⟨boundaryInclusion,
      continuous_boundaryInclusion⟩ boundaryBase g) =
      Multiplicative.ofAdd (boundaryCoord g).toAdd.2
  right_leg : ∀ g,
    rightCoord (FundamentalGroup.map
      ⟨boundaryInclusion ∘ h,
        continuous_boundaryInclusion.comp h.continuous⟩ boundaryBase g) =
      Multiplicative.ofAdd
        (2 * (boundaryCoord g).toAdd.1 + d * (boundaryCoord g).toAdd.2)

#print axioms coordinateLeftLeg
#print axioms coordinateRightLeg
#print axioms CoordinatePseudoCocone
#print axioms CoordinatePseudoCoconeHom
#print axioms postcomposeCoordinatePseudoCoconeFunctor
#print axioms actual_left_leg_in_coordinates
#print axioms actual_right_leg_in_coordinates
#print axioms BasedTwiceSpiralCoordinateInterface

end ConstructionTargets.TwiceSpiralFundamentalGroupoidCoordinates
