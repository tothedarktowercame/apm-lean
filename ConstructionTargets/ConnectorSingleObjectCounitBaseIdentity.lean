import ConstructionTargets.ConnectedGroupoidSingleObjEquivalence

open CategoryTheory
noncomputable section

namespace ConstructionTargets.ConnectorSingleObjectCounitBaseIdentity

open ConstructionTargets.ConnectedGroupoidVertexReconstruction
open ConstructionTargets.ConnectedGroupoidSingleObjEquivalence

universe u v
variable {G : Type u} [Groupoid.{v} G]

/-- The counit at the single object is the connector at the base (no chosen
isomorphism since `connectorSingleObjEquivalence` has an explicit inverse). -/
theorem connectorSingleObjEquivalence_counit_base_eq_connector
    (S : ConnectorSystem G) :
    (connectorSingleObjEquivalence S).counitIso.hom.app
      (SingleObj.star (End S.base)) = ((S.connector S.base).hom : End S.base) := rfl

theorem connectorSingleObjEquivalence_counit_base_identity_of_connector
    (S : ConnectorSystem G) (h : S.connector S.base = Iso.refl _) :
    (connectorSingleObjEquivalence S).counitIso.hom.app
      (SingleObj.star (End S.base)) = 𝟙 _ := by
  rw [connectorSingleObjEquivalence_counit_base_eq_connector, h]
  rfl

#print axioms connectorSingleObjEquivalence_counit_base_eq_connector
#print axioms connectorSingleObjEquivalence_counit_base_identity_of_connector

end ConstructionTargets.ConnectorSingleObjectCounitBaseIdentity
