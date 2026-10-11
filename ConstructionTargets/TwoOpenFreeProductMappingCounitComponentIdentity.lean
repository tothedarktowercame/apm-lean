import ConstructionTargets.TwoOpenFreeProductMappingInverseIdentityLegCoordinates

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenFreeProductMappingCounitComponentIdentity

open TwoOpenLegCompatibleConnectorSystems
open GenericTargetNaturalSourceReconstructionLegCoordinates
open TwoOpenFreeProductMappingInverseIdentityLegCoordinates

variable {X : Type} [TopologicalSpace X] {U V : Set X}
variable [PathConnectedSpace U] [PathConnectedSpace V]
variable [SimplyConnectedSpace (U ∩ V : Set X)]

theorem inverseIdentity_map_eq_of_counit_component_identity
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X))
    (hc :
    (inverseIdentityCounit hU hV hcover w).hom.app
        (SingleObj.star (Monoid.Coprod (End (leftConnectors w).base)
          (End (rightConnectors w).base))) = 𝟙 _)
    (g : End (SingleObj.star (Monoid.Coprod (End (leftConnectors w).base)
      (End (rightConnectors w).base)))) :
    ((TwoOpenFreeProductMapping.mapping (FreeProductTarget w)
        hU hV hcover w).functor.obj
      (inverseIdentityFunctor hU hV hcover w)).map g = g := by
  have hn := inverseIdentityCounit_naturality hU hV hcover w g
  rw [hc] at hn
  exact (Category.comp_id _).symm.trans (hn.trans (Category.id_comp _))

#print axioms inverseIdentity_map_eq_of_counit_component_identity

end ConstructionTargets.TwoOpenFreeProductMappingCounitComponentIdentity
