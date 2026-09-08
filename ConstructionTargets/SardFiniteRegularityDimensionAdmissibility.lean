import Mathlib

namespace SardFiniteRegularityDimensionAdmissibilityProbe

/-- The Taylor-covering regularity order is admissible when its target-scaled
exponent strictly exceeds the source dimension. -/
def FiniteOrderAdmissible (sourceDim targetDim order : ℕ) : Prop :=
  sourceDim < (order + 1) * targetDim

theorem finiteOrderAdmissible_of_positive_surplus
    {sourceDim targetDim order surplus : ℕ}
    (hsurplus : 0 < surplus)
    (hidentity : (order + 1) * targetDim = sourceDim + surplus) :
    FiniteOrderAdmissible sourceDim targetDim order := by
  unfold FiniteOrderAdmissible
  omega

#print axioms finiteOrderAdmissible_of_positive_surplus

end SardFiniteRegularityDimensionAdmissibilityProbe
