import ConstructionTargets.SardClassicalRegularityAdmissibility

namespace SardRankDropRegularityAdmissibilityProbe

/-- Classical Sard admissibility is preserved when the same derivative rank
is removed from source and target dimensions. -/
theorem sardOrderAdmissible_sub_rank
    {sourceDim targetDim order rank : ℕ}
    (h : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      sourceDim targetDim order)
    (hrSource : rank ≤ sourceDim) (hrTarget : rank ≤ targetDim) :
    SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (sourceDim - rank) (targetDim - rank) order := by
  unfold SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible at *
  omega

#print axioms sardOrderAdmissible_sub_rank

end SardRankDropRegularityAdmissibilityProbe
