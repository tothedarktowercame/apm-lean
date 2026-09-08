import Mathlib

namespace SardClassicalRegularityAdmissibilityProbe

/-- Classical finite-order Morse--Sard admissibility: the differentiability
order exceeds the source-minus-target dimension deficit. -/
def SardOrderAdmissible (sourceDim targetDim order : ℕ) : Prop :=
  sourceDim < targetDim + order

theorem sardOrderAdmissible_of_deficit_lt_order
    {sourceDim targetDim order : ℕ}
    (hdeficit : sourceDim - targetDim < order) :
    SardOrderAdmissible sourceDim targetDim order := by
  unfold SardOrderAdmissible
  omega

theorem sardOrderAdmissible_mono_order
    {sourceDim targetDim k l : ℕ}
    (h : SardOrderAdmissible sourceDim targetDim k) (hkl : k ≤ l) :
    SardOrderAdmissible sourceDim targetDim l := by
  unfold SardOrderAdmissible at *
  omega

#print axioms sardOrderAdmissible_of_deficit_lt_order
#print axioms sardOrderAdmissible_mono_order

end SardClassicalRegularityAdmissibilityProbe
