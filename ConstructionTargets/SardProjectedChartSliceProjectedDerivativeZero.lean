import ConstructionTargets.SardRankUpperResidualSliceAnnihilation
import ConstructionTargets.SardEventuallyConstantCoordinateSliceFlatness
import ConstructionTargets.SardProjectedInverseChartSliceConstancy

open Filter
open scoped Topology

namespace SardProjectedChartSliceProjectedDerivativeZeroProbe

variable {E R G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The derivative of a fixed-first-coordinate inverse-chart slice is killed
by the derivative of that coordinate map. -/
theorem projected_deriv_comp_sliceDeriv_eq_zero
    (chart : OpenPartialHomeomorph E (R × G)) (p : E → R)
    (hfirst : (fun x => (chart x).1) = p)
    (r : R) (z : G) (hz : (r, z) ∈ chart.target)
    (P : E →L[ℝ] R) (J : G →L[ℝ] E)
    (hp : HasFDerivAt p P (chart.symm (r, z)))
    (hslice : HasFDerivAt (fun w : G => chart.symm (r, w)) J z) :
    P.comp J = 0 := by
  apply SardEventuallyConstantCoordinateSliceFlatnessProbe.derivative_comp_eq_zero_of_coordinate_eventually_constant
    p (fun w : G => chart.symm (r, w)) r z P J hp hslice
  apply SardProjectedInverseChartSliceConstancyProbe.eventually_firstCoordinate_inverse_fixedSlice
    chart.symm p r z chart.target (chart.open_target.mem_nhds hz)
  intro q hq
  rw [← congrFun hfirst (chart.symm q), chart.right_inv hq]

#print axioms projected_deriv_comp_sliceDeriv_eq_zero

end SardProjectedChartSliceProjectedDerivativeZeroProbe
