import ConstructionTargets.SardDerivativeRankUpperCompactExhaustion

open Set

namespace SardClosedOpenCompactExhaustionProbe

/-- A closed locus localized to an open chart in a locally compact,
second-countable space has an ambient countable compact exhaustion. -/
theorem exists_compact_cover_inter_of_isClosed_isOpen
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X]
    (s U : Set X) (hs : IsClosed s) (hU : IsOpen U) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s ∩ U := by
  letI : LocallyCompactSpace U := hU.locallyCompactSpace
  have ht_closed : IsClosed {x : U | (x : X) ∈ s} :=
    hs.preimage continuous_subtype_val
  have ht : IsSigmaCompact {x : U | (x : X) ∈ s} :=
    isSigmaCompact_univ.of_isClosed_subset ht_closed (subset_univ _)
  have himage : IsSigmaCompact ((↑) '' {x : U | (x : X) ∈ s} : Set X) :=
    Subtype.isSigmaCompact_iff.mp ht
  have heq : ((↑) '' {x : U | (x : X) ∈ s} : Set X) = s ∩ U := by
    ext x
    simp [and_comm]
  rw [heq] at himage
  exact himage

#print axioms exists_compact_cover_inter_of_isClosed_isOpen

end SardClosedOpenCompactExhaustionProbe
