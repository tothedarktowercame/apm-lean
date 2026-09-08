import ConstructionTargets.SardProjectedDerivativeSurjectiveOfRightInverse
import Mathlib.Analysis.Calculus.FDeriv.Congr

namespace SardOpenPartialHomeomorphDerivativeRightInverseProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiating the local right-inverse identity of an open partial
homeomorphism gives a right inverse for its derivative. -/
theorem derivative_comp_inverseDerivative_eq_id
    (chart : OpenPartialHomeomorph E F) (y : F) (hy : y ∈ chart.target)
    (D : E →L[ℝ] F) (H : F →L[ℝ] E)
    (hD : HasFDerivAt chart D (chart.symm y))
    (hH : HasFDerivAt chart.symm H y) :
    D.comp H = ContinuousLinearMap.id ℝ F := by
  have hcomp : HasFDerivAt (fun z => chart (chart.symm z)) (D.comp H) y :=
    hD.comp y hH
  have heq : (fun z => chart (chart.symm z)) =ᶠ[nhds y] fun z => z :=
    chart.eventually_right_inverse hy
  have hid : HasFDerivAt (fun z : F => z) (ContinuousLinearMap.id ℝ F) y :=
    hasFDerivAt_id y
  exact (heq.hasFDerivAt_iff.mp hcomp).unique hid

#print axioms derivative_comp_inverseDerivative_eq_id

end SardOpenPartialHomeomorphDerivativeRightInverseProbe
