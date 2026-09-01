import ConstructionTargets.ConnectedGroupoidVertexReconstruction
import Mathlib.CategoryTheory.SingleObj

/-!
# A connected groupoid as the single-object category of a vertex group

An explicit connector system gives a normal-form functor from the groupoid to
the single-object category of endomorphisms of its chosen base.  The connector
calculus proves this functor faithful and constructively full; its constant
object map is essentially surjective.
-/

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConnectedGroupoidSingleObjEquivalence

open ConstructionTargets.ConnectedGroupoidVertexReconstruction

universe u v
variable {G : Type u} [Groupoid.{v} G]

def normalFormFunctor (S : ConnectorSystem G) :
    G ⥤ SingleObj (End S.base) where
  obj _ := SingleObj.star (End S.base)
  map f := S.normalForm f
  map_id X := S.normalForm_id X
  map_comp f g := S.normalForm_comp f g

instance normalFormFunctor_faithful (S : ConnectorSystem G) :
    (normalFormFunctor S).Faithful where
  map_injective := by
    intro X Y f g h
    exact S.normalForm_injective h

instance normalFormFunctor_full (S : ConnectorSystem G) :
    (normalFormFunctor S).Full where
  map_surjective {X Y} f := by
    let g : X ⟶ Y := (S.connector X).inv ≫ f ≫ (S.connector Y).hom
    refine ⟨g, ?_⟩
    change S.normalForm g = f
    simp [g, ConnectorSystem.normalForm, Category.assoc]

instance normalFormFunctor_essSurj (S : ConnectorSystem G) :
    (normalFormFunctor S).EssSurj where
  mem_essImage X := by
    cases X
    exact ⟨S.base, ⟨Iso.refl _⟩⟩

instance normalFormFunctor_isEquivalence (S : ConnectorSystem G) :
    (normalFormFunctor S).IsEquivalence :=
  Functor.IsEquivalence.mk

def connectorSingleObjEquivalence (S : ConnectorSystem G) :
    G ≌ SingleObj (End S.base) :=
  (normalFormFunctor S).asEquivalence

@[simp] theorem connectorSingleObjEquivalence_functor_obj
    (S : ConnectorSystem G) (X : G) :
    (connectorSingleObjEquivalence S).functor.obj X =
      SingleObj.star (End S.base) := rfl

@[simp] theorem connectorSingleObjEquivalence_functor_map
    (S : ConnectorSystem G) {X Y : G} (f : X ⟶ Y) :
    (connectorSingleObjEquivalence S).functor.map f = S.normalForm f := rfl

#print axioms connectorSingleObjEquivalence
#print axioms connectorSingleObjEquivalence_functor_map

end ConstructionTargets.ConnectedGroupoidSingleObjEquivalence
