import ConstructionTargets.TwoOpenFreeProductMapping

open Set Topology
noncomputable section

namespace ConstructionTargets.TwoOpenFreeProductGroupEquivalenceCoordinates

open TwoOpenFreeProductMapping

variable {X : Type} [TopologicalSpace X] {U V : Set X}

def leftInclusion : C(U, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def rightInclusion : C(V, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

structure TwoOpenGroupEquivalenceCoordinates
    [PathConnectedSpace U] [PathConnectedSpace V]
    [SimplyConnectedSpace (U ∩ V : Set X)]
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (w : (U ∩ V : Set X)) : Prop where
  left : ∀ g : FundamentalGroup U ⟨w.1, w.2.1⟩,
    groupEquivalence hU hV hcover w
        (FundamentalGroup.map leftInclusion ⟨w.1, w.2.1⟩ g) =
      Monoid.Coprod.inl g
  right : ∀ g : FundamentalGroup V ⟨w.1, w.2.2⟩,
    groupEquivalence hU hV hcover w
        (FundamentalGroup.map rightInclusion ⟨w.1, w.2.2⟩ g) =
      Monoid.Coprod.inr g

end ConstructionTargets.TwoOpenFreeProductGroupEquivalenceCoordinates
