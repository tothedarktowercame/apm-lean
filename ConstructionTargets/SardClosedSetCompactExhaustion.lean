import ConstructionTargets.SardCountableCompactImageNullity

open Set

namespace SardClosedSetCompactExhaustionProbe

/-- A closed subset of a sigma-compact space has a natural-number-indexed
compact cover with exact union. -/
theorem exists_countable_compact_cover_of_isClosed
    {X : Type*} [TopologicalSpace X] [SigmaCompactSpace X]
    (s : Set X) (hs : IsClosed s) :
    ∃ K : ℕ → Set X, (∀ n, IsCompact (K n)) ∧ ⋃ n, K n = s := by
  exact isSigmaCompact_univ.of_isClosed_subset hs (subset_univ s)

#print axioms exists_countable_compact_cover_of_isClosed

end SardClosedSetCompactExhaustionProbe
