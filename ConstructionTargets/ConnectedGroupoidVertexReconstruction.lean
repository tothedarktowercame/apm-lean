import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Algebra.Group.Hom.Basic

/-!
# Reconstructing a connected groupoid from one vertex group

A connector system chooses a base object and an isomorphism from it to every
object.  Conjugating a morphism by these connectors gives its vertex-group
normal form.  This file proves the normal-form identity and composition laws
and packages constant-object representations as functors.
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConnectedGroupoidVertexReconstruction

universe u v u' v'

variable {G : Type u} [Groupoid.{v} G]

/-- A chosen base object and explicit connectors from it to every object. -/
structure ConnectorSystem (G : Type u) [Groupoid.{v} G] where
  base : G
  connector : ∀ X : G, base ≅ X

namespace ConnectorSystem

variable (S : ConnectorSystem G)

/-- The vertex-group normal form of an arbitrary groupoid morphism. -/
def normalForm {X Y : G} (f : X ⟶ Y) : S.base ⟶ S.base :=
  (S.connector X).hom ≫ f ≫ (S.connector Y).inv

@[simp] theorem normalForm_id (X : G) :
    S.normalForm (𝟙 X) = 𝟙 S.base := by
  simp [normalForm]

theorem normalForm_comp {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    S.normalForm (f ≫ g) = S.normalForm f ≫ S.normalForm g := by
  simp only [normalForm, Category.assoc]
  rw [← Category.assoc (S.connector Y).inv (S.connector Y).hom,
    (S.connector Y).inv_hom_id, Category.id_comp]

/-- Recover a morphism from its normal form and the endpoint connectors. -/
theorem reconstruct {X Y : G} (f : X ⟶ Y) :
    (S.connector X).inv ≫ S.normalForm f ≫ (S.connector Y).hom = f := by
  simp [normalForm, Category.assoc]

/-- Equality of normal forms detects equality of the original arrows. -/
theorem normalForm_injective {X Y : G} :
    Function.Injective (S.normalForm : (X ⟶ Y) → (S.base ⟶ S.base)) := by
  intro f g h
  have := congrArg (fun k =>
    (S.connector X).inv ≫ k ≫ (S.connector Y).hom) h
  simpa only [S.reconstruct] using this

/-- A representation of the chosen vertex group on one object of another
groupoid extends to a functor, constant on objects. -/
def constantObjectFunctor {H : Type u'} [Groupoid.{v'} H] (Z : H)
    (ρ : MonoidHom (End S.base) (End Z)) : Functor G H where
  obj _ := Z
  map f := ρ (S.normalForm f)
  map_id X := by
    rw [S.normalForm_id]
    change ρ (1 : End S.base) = (1 : End Z)
    exact map_one ρ
  map_comp f g := by
    rw [S.normalForm_comp]
    change ρ (End.of (S.normalForm g) * End.of (S.normalForm f)) =
      ρ (End.of (S.normalForm g)) * ρ (End.of (S.normalForm f))
    exact map_mul ρ _ _

@[simp] theorem constantObjectFunctor_obj
    {H : Type u'} [Groupoid.{v'} H] (Z : H)
    (ρ : MonoidHom (End S.base) (End Z)) (X : G) :
    (S.constantObjectFunctor Z ρ).obj X = Z := rfl

@[simp] theorem constantObjectFunctor_map
    {H : Type u'} [Groupoid.{v'} H] (Z : H)
    (ρ : MonoidHom (End S.base) (End Z))
    {X Y : G} (f : X ⟶ Y) :
    (S.constantObjectFunctor Z ρ).map f = ρ (S.normalForm f) := rfl

#print axioms normalForm_id
#print axioms normalForm_comp
#print axioms reconstruct
#print axioms normalForm_injective
#print axioms constantObjectFunctor

end ConnectorSystem

end ConstructionTargets.ConnectedGroupoidVertexReconstruction
