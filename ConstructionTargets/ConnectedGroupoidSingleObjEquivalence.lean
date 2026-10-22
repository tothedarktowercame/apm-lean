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

universe u v u' v'
variable {G : Type u} [Groupoid.{v} G]
variable {H : Type u'} [Groupoid.{v'} H]

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

/-- The base inclusion: the single object goes to the chosen base and a vertex-group
element is itself. -/
def baseInclusionFunctor (S : ConnectorSystem G) :
    SingleObj (End S.base) ⥤ G where
  obj _ := S.base
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The equivalence with explicit inverse `baseInclusionFunctor`; the unit is given by
the connectors and the counit at the single object is the connector at the base.
No component is chosen (this replaced `Functor.asEquivalence`, whose counit came from
`Classical.choice`, after job 2346). -/
def connectorSingleObjEquivalence (S : ConnectorSystem G) :
    G ≌ SingleObj (End S.base) where
  functor := normalFormFunctor S
  inverse := baseInclusionFunctor S
  unitIso := NatIso.ofComponents (fun X => (S.connector X).symm) (by
    intro X Y f
    change f ≫ (S.connector Y).inv =
      (S.connector X).inv ≫ ((S.connector X).hom ≫ f ≫ (S.connector Y).inv)
    simp)
  counitIso := NatIso.ofComponents
    (fun _ =>
      { hom := (S.connector S.base).hom
        inv := (S.connector S.base).inv
        hom_inv_id := (S.connector S.base).hom_inv_id
        inv_hom_id := (S.connector S.base).inv_hom_id }) (by
    intro X Y f
    change ((S.connector S.base).hom ≫ f ≫ (S.connector S.base).inv) ≫
        (S.connector S.base).hom = (S.connector S.base).hom ≫ f
    simp [Category.assoc])
  functor_unitIso_comp X := by
    change ((S.connector X).hom ≫ (S.connector X).inv ≫ (S.connector S.base).inv) ≫
        (S.connector S.base).hom = 𝟙 S.base
    simp

@[simp] theorem connectorSingleObjEquivalence_functor_obj
    (S : ConnectorSystem G) (X : G) :
    (connectorSingleObjEquivalence S).functor.obj X =
      SingleObj.star (End S.base) := rfl

@[simp] theorem connectorSingleObjEquivalence_functor_map
    (S : ConnectorSystem G) {X Y : G} (f : X ⟶ Y) :
    (connectorSingleObjEquivalence S).functor.map f = S.normalForm f := rfl

@[simp] theorem connectorSingleObjEquivalence_inverse_obj
    (S : ConnectorSystem G) (x : SingleObj (End S.base)) :
    (connectorSingleObjEquivalence S).inverse.obj x = S.base := rfl

@[simp] theorem connectorSingleObjEquivalence_inverse_map
    (S : ConnectorSystem G) {x y : SingleObj (End S.base)} (f : x ⟶ y) :
    (connectorSingleObjEquivalence S).inverse.map f = (f : End S.base) := rfl

theorem connectorSingleObjEquivalence_counit_hom_app
    (S : ConnectorSystem G) (x : SingleObj (End S.base)) :
    (connectorSingleObjEquivalence S).counitIso.hom.app x =
      ((S.connector S.base).hom : End S.base) := rfl

def inducedVertexHom (F : G ⥤ H) (SG : ConnectorSystem G)
    (SH : ConnectorSystem H) (hbase : F.obj SG.base = SH.base) :
    End SG.base →* End SH.base where
  toFun f := eqToHom hbase.symm ≫ F.map f ≫ eqToHom hbase
  map_one' := by
    change eqToHom hbase.symm ≫ F.map (𝟙 SG.base) ≫ eqToHom hbase =
      𝟙 SH.base
    rw [F.map_id]
    simp
  map_mul' f g := by
    change eqToHom hbase.symm ≫ F.map (g ≫ f) ≫ eqToHom hbase =
      (eqToHom hbase.symm ≫ F.map g ≫ eqToHom hbase) ≫
        (eqToHom hbase.symm ≫ F.map f ≫ eqToHom hbase)
    rw [F.map_comp]
    simp [Category.assoc]

theorem inducedVertexHom_apply (F : G ⥤ H) (SG : ConnectorSystem G)
    (SH : ConnectorSystem H) (hbase : F.obj SG.base = SH.base)
    (f : End SG.base) :
    inducedVertexHom F SG SH hbase f =
      eqToHom hbase.symm ≫ F.map f ≫ eqToHom hbase := rfl

theorem normalForm_map
    (F : G ⥤ H) (SG : ConnectorSystem G) (SH : ConnectorSystem H)
    (hbase : F.obj SG.base = SH.base)
    (hconnector : ∀ X : G,
      F.mapIso (SG.connector X) =
        (eqToIso hbase).trans (SH.connector (F.obj X)))
    {X Y : G} (f : X ⟶ Y) :
    SH.normalForm (F.map f) =
      inducedVertexHom F SG SH hbase (SG.normalForm f) := by
  simp only [ConnectorSystem.normalForm, inducedVertexHom_apply]
  have hx : F.map (SG.connector X).hom =
      eqToHom hbase ≫ (SH.connector (F.obj X)).hom := by
    simpa using congrArg Iso.hom (hconnector X)
  have hy : F.map (SG.connector Y).inv =
      (SH.connector (F.obj Y)).inv ≫ eqToHom hbase.symm := by
    simpa using congrArg Iso.inv (hconnector Y)
  have hx' : (SH.connector (F.obj X)).hom =
      eqToHom hbase.symm ≫ F.map (SG.connector X).hom := by
    rw [hx, ← Category.assoc]
    simp
  have hy' : (SH.connector (F.obj Y)).inv =
      F.map (SG.connector Y).inv ≫ eqToHom hbase := by
    rw [hy, Category.assoc]
    simp
  rw [hx', hy', F.map_comp, F.map_comp]
  simp only [Category.assoc]

def normalFormComparison
    (F : G ⥤ H) (SG : ConnectorSystem G) (SH : ConnectorSystem H)
    (hbase : F.obj SG.base = SH.base)
    (hconnector : ∀ X : G,
      F.mapIso (SG.connector X) =
        (eqToIso hbase).trans (SH.connector (F.obj X))) :
    F ⋙ normalFormFunctor SH ≅
      normalFormFunctor SG ⋙ (inducedVertexHom F SG SH hbase).toFunctor :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    change SH.normalForm (F.map f) ≫ 𝟙 _ =
      𝟙 _ ≫ inducedVertexHom F SG SH hbase (SG.normalForm f)
    simp only [Category.comp_id, Category.id_comp]
    exact normalForm_map F SG SH hbase hconnector f)

@[simp] theorem normalFormComparison_hom_app
    (F : G ⥤ H) (SG : ConnectorSystem G) (SH : ConnectorSystem H)
    (hbase : F.obj SG.base = SH.base)
    (hconnector : ∀ X : G,
      F.mapIso (SG.connector X) =
        (eqToIso hbase).trans (SH.connector (F.obj X))) (X : G) :
    (normalFormComparison F SG SH hbase hconnector).hom.app X = 𝟙 _ := rfl

@[simp] theorem normalFormComparison_inv_app
    (F : G ⥤ H) (SG : ConnectorSystem G) (SH : ConnectorSystem H)
    (hbase : F.obj SG.base = SH.base)
    (hconnector : ∀ X : G,
      F.mapIso (SG.connector X) =
        (eqToIso hbase).trans (SH.connector (F.obj X))) (X : G) :
    (normalFormComparison F SG SH hbase hconnector).inv.app X = 𝟙 _ := rfl

def isoWhiskerLeft {C D E : Type*} [Category C] [Category D] [Category E]
    (L : C ⥤ D) {F G : D ⥤ E} (α : F ≅ G) : L ⋙ F ≅ L ⋙ G where
  hom := Functor.whiskerLeft L α.hom
  inv := Functor.whiskerLeft L α.inv
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

def isoWhiskerRight {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (α : F ≅ G) (R : D ⥤ E) : F ⋙ R ≅ G ⋙ R where
  hom := Functor.whiskerRight α.hom R
  inv := Functor.whiskerRight α.inv R
  hom_inv_id := by
    ext X
    change R.map (α.hom.app X) ≫ R.map (α.inv.app X) = 𝟙 _
    rw [← R.map_comp]
    simp
  inv_hom_id := by
    ext X
    change R.map (α.inv.app X) ≫ R.map (α.hom.app X) = 𝟙 _
    rw [← R.map_comp]
    simp

def connectorFunctorComparison
    (F : G ⥤ H) (SG : ConnectorSystem G) (SH : ConnectorSystem H)
    (hbase : F.obj SG.base = SH.base)
    (hconnector : ∀ X : G,
      F.mapIso (SG.connector X) =
        (eqToIso hbase).trans (SH.connector (F.obj X))) :
    (connectorSingleObjEquivalence SG).inverse ⋙ F ⋙
        (connectorSingleObjEquivalence SH).functor ≅
      (inducedVertexHom F SG SH hbase).toFunctor :=
  (Functor.associator (connectorSingleObjEquivalence SG).inverse F
      (connectorSingleObjEquivalence SH).functor).trans
    ((isoWhiskerLeft (connectorSingleObjEquivalence SG).inverse
      (normalFormComparison F SG SH hbase hconnector)).trans
    ((Functor.associator (connectorSingleObjEquivalence SG).inverse
      (connectorSingleObjEquivalence SG).functor
      (inducedVertexHom F SG SH hbase).toFunctor).symm.trans
    ((isoWhiskerRight (connectorSingleObjEquivalence SG).counitIso
      (inducedVertexHom F SG SH hbase).toFunctor).trans
      (Functor.leftUnitor (inducedVertexHom F SG SH hbase).toFunctor))))

#print axioms connectorSingleObjEquivalence
#print axioms connectorSingleObjEquivalence_functor_map
#print axioms inducedVertexHom
#print axioms normalForm_map
#print axioms normalFormComparison
#print axioms connectorFunctorComparison

end ConstructionTargets.ConnectedGroupoidSingleObjEquivalence
