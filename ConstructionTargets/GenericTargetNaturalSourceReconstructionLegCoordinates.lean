import ConstructionTargets.TwoOpenFreeProductGroupEquivalenceCoordinates

open Set CategoryTheory
noncomputable section

namespace ConstructionTargets.GenericTargetNaturalSourceReconstructionLegCoordinates

open TwoOpenFreeProductMapping TwoOpenLegCompatibleConnectorSystems

variable {X : Type} [TopologicalSpace X] {U V : Set X}
variable [PathConnectedSpace U] [PathConnectedSpace V]
variable [SimplyConnectedSpace (U ∩ V : Set X)]

abbrev FreeProductTarget (w : (U ∩ V : Set X)) :=
  SingleObj (Monoid.Coprod (End (leftConnectors w).base)
    (End (rightConnectors w).base))

/-- The functor reconstructed by target-natural Yoneda is literally the
inverse image of the identity functor under the two-open mapping equivalence.
This is the normalization boundary at which leg-coordinate compatibility must
be established. -/
theorem sourceEquivalence_functor_eq_mapping_inverse_identity
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X)) :
    (sourceEquivalence hU hV hcover w).functor =
      (mapping (FreeProductTarget w) hU hV hcover w).inverse.obj
        (Functor.id (FreeProductTarget w)) :=
  rfl

#print axioms sourceEquivalence_functor_eq_mapping_inverse_identity

end ConstructionTargets.GenericTargetNaturalSourceReconstructionLegCoordinates
