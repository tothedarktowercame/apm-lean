import ConstructionTargets.SardClassicalRegularityAdmissibility

namespace SardFiniteOrderTaylorBudgetEndpointProbe

theorem taylorBudget_strict_or_endpoint
    {sourceDim targetDim order : ℕ}
    (htarget : 0 < targetDim) (horder : 0 < order)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      sourceDim targetDim order) :
    (∃ d : ℕ, 0 < d ∧ order * targetDim = sourceDim + d) ∨
      order * targetDim = sourceDim := by
  have hle : sourceDim ≤ order * targetDim := by
    unfold SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible at hadm
    have hprod : 0 ≤ (order - 1) * (targetDim - 1) := Nat.zero_le _
    nlinarith
  rcases hle.eq_or_lt with h | h
  · exact Or.inr h.symm
  · left
    refine ⟨order * targetDim - sourceDim, Nat.sub_pos_iff_lt.mpr h, ?_⟩
    omega

#print axioms taylorBudget_strict_or_endpoint
end SardFiniteOrderTaylorBudgetEndpointProbe
