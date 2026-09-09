import ConstructionTargets.SardFiniteOrderTaylorBudgetEndpoint

namespace SardFiniteOrderTaylorEndpointClassificationProbe

theorem endpoint_order_eq_one_or_targetDim_eq_one
    {sourceDim targetDim order : ℕ}
    (htarget : 0 < targetDim) (horder : 0 < order)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      sourceDim targetDim order)
    (hendpoint : order * targetDim = sourceDim) :
    order = 1 ∨ targetDim = 1 := by
  unfold SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible at hadm
  by_contra h
  push_neg at h
  have ho : 2 ≤ order := by omega
  have ht : 2 ≤ targetDim := by omega
  nlinarith

#print axioms endpoint_order_eq_one_or_targetDim_eq_one
end SardFiniteOrderTaylorEndpointClassificationProbe
