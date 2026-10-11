import ConstructionTargets.GenericTargetNaturalSourceReconstructionLegCoordinates

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.TwoOpenFreeProductMappingInverseIdentityLegCoordinates

open TwoOpenFreeProductMapping TwoOpenLegCompatibleConnectorSystems
open GenericTargetNaturalSourceReconstructionLegCoordinates

variable {X : Type} [TopologicalSpace X] {U V : Set X}
variable [PathConnectedSpace U] [PathConnectedSpace V]
variable [SimplyConnectedSpace (U ∩ V : Set X)]

def inverseIdentityFunctor
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X)) : Functor (FundamentalGroupoid X) (FreeProductTarget w) :=
  (mapping (FreeProductTarget w) hU hV hcover w).inverse.obj
    (Functor.id (FreeProductTarget w))

/-- The mapping equivalence identifies its inverse image of the identity with
the identity only by its counit isomorphism. -/
def inverseIdentityCounit
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X)) :
    (mapping (FreeProductTarget w) hU hV hcover w).functor.obj
        (inverseIdentityFunctor hU hV hcover w) ≅
      Functor.id (FreeProductTarget w) :=
  (mapping (FreeProductTarget w) hU hV hcover w).counitIso.app _

/-- Consequently, the available theorem for an inverse-image morphism is a
conjugacy equation involving the counit component. Literal equality requires
an additional normalization of that component. -/
theorem inverseIdentityCounit_naturality
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X))
    {a b : FreeProductTarget w} (g : a ⟶ b) :
    ((mapping (FreeProductTarget w) hU hV hcover w).functor.obj
        (inverseIdentityFunctor hU hV hcover w)).map g ≫
        (inverseIdentityCounit hU hV hcover w).hom.app b =
      (inverseIdentityCounit hU hV hcover w).hom.app a ≫ g :=
  (inverseIdentityCounit hU hV hcover w).hom.naturality g

#print axioms inverseIdentityCounit_naturality

end ConstructionTargets.TwoOpenFreeProductMappingInverseIdentityLegCoordinates
