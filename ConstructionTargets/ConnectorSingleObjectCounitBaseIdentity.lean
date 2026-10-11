import ConstructionTargets.ConnectedGroupoidSingleObjEquivalence

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConnectorSingleObjectCounitBaseIdentity

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.ConnectedGroupoidSingleObjEquivalence

universe u v
variable {G : Type u} [Groupoid.{v} G]

theorem connectorSingleObjEquivalence_counit_base_eq_chosenIso
    (S : ConnectorSystem G) :
    (connectorSingleObjEquivalence S).counitIso.hom.app
      (SingleObj.star (End S.base)) =
        ((normalFormFunctor S).objObjPreimageIso
          (SingleObj.star (End S.base))).hom := rfl

/-- The requested identity is exactly a normalization of the isomorphism
chosen from the `Nonempty` witness in `EssSurj.mem_essImage`.  The existing
`Functor.asEquivalence` API supplies no such normalization. -/
theorem connectorSingleObjEquivalence_counit_base_identity_iff
    (S : ConnectorSystem G) :
    ((connectorSingleObjEquivalence S).counitIso.hom.app
      (SingleObj.star (End S.base)) = 𝟙 _) ↔
      ((normalFormFunctor S).objObjPreimageIso
        (SingleObj.star (End S.base))).hom = 𝟙 _ := by
  rw [connectorSingleObjEquivalence_counit_base_eq_chosenIso]
  constructor <;> intro h <;>
    simpa [connectorSingleObjEquivalence, Functor.asEquivalence,
      Functor.inv] using h

#print axioms connectorSingleObjEquivalence_counit_base_eq_chosenIso
#print axioms connectorSingleObjEquivalence_counit_base_identity_iff

end ConstructionTargets.ConnectorSingleObjectCounitBaseIdentity
