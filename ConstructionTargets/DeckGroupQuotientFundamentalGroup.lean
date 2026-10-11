import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Homotopy.Lifting

open Topology

namespace ConstructionTargets.DeckGroupQuotientFundamentalGroup

/-- The orbit projection of a free properly discontinuous action is a covering
map under the separation and local compactness hypotheses used by Mathlib's
quotient-covering construction. -/
theorem quotientMk_isCoveringMap
    {G X : Type*} [Group G] [TopologicalSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    [LocallyCompactSpace X] [T2Space X]
    (free : ∀ g : G, ∀ x : X, g • x = x → g = 1) :
    IsCoveringMap
      (Quotient.mk (MulAction.orbitRel G X) :
        X → MulAction.orbitRel.Quotient G X) := by
  letI : IsCancelSMul G X :=
    isCancelSMul_iff_eq_one_of_smul_eq.mpr free
  exact
    (isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul
      (G := G) (E := X)).isCoveringMap

#print axioms quotientMk_isCoveringMap

end ConstructionTargets.DeckGroupQuotientFundamentalGroup
