import ConstructionTargets.TwoOpenFreeProductMappingCounitComponentIdentity

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenFreeProductMappingCompositeCounitIdentity

open TwoOpenLegCompatibleConnectorSystems
open GenericTargetNaturalSourceReconstructionLegCoordinates
open TwoOpenFreeProductMappingInverseIdentityLegCoordinates

variable {X : Type} [TopologicalSpace X] {U V : Set X}
variable [PathConnectedSpace U] [PathConnectedSpace V]
variable [SimplyConnectedSpace (U ∩ V : Set X)]

/-- The precise five-equivalence counit component whose normalization is
needed for literal, rather than conjugated, free-product coordinates. -/
def compositeCounitComponent
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X)) :=
  (inverseIdentityCounit hU hV hcover w).hom.app
    (SingleObj.star (Monoid.Coprod (End (leftConnectors w).base)
      (End (rightConnectors w).base)))

theorem inverseIdentityCounit_component_eq_compositeCounitComponent
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X)) :
    (inverseIdentityCounit hU hV hcover w).hom.app
        (SingleObj.star (Monoid.Coprod (End (leftConnectors w).base)
          (End (rightConnectors w).base))) =
      compositeCounitComponent hU hV hcover w :=
  rfl

#print axioms inverseIdentityCounit_component_eq_compositeCounitComponent

end ConstructionTargets.TwoOpenFreeProductMappingCompositeCounitIdentity
