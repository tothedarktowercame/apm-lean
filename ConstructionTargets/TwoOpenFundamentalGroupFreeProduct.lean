import ConstructionTargets.TwoOpenFundamentalGroupoidPseudopushout
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.GroupTheory.Coprod.Basic

/-!
# Two-open fundamental-group free-product principle

This file records the exact reusable proposition needed to pass from the
two-open fundamental-groupoid pseudopushout to a chosen-basepoint free-product
description.  It deliberately keeps the basepoints in the two open pieces
explicit.
-/

open Set

namespace ConstructionTargets.TwoOpenFundamentalGroupFreeProduct

/-- The generic two-open van Kampen principle at chosen basepoints: if two
path-connected open sets cover a space and their overlap is simply connected,
then the ambient fundamental group is (noncanonically) the free product of the
two piece fundamental groups. -/
def twoOpenFundamentalGroupFreeProduct : Prop :=
  ∀ (X : Type) [TopologicalSpace X]
    (U V : Set X) (x : X) (u : U) (v : V),
    IsOpen U → IsOpen V → U ∪ V = Set.univ →
    PathConnectedSpace U → PathConnectedSpace V →
    SimplyConnectedSpace (U ∩ V : Set X) → Nonempty
      (FundamentalGroup X x ≃*
        Monoid.Coprod (FundamentalGroup U u) (FundamentalGroup V v))

#print axioms twoOpenFundamentalGroupFreeProduct

end ConstructionTargets.TwoOpenFundamentalGroupFreeProduct
