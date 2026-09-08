import ConstructionTargets.SardProjectedChartInverseSliceCompositionContDiff

namespace SardProjectedChartInverseSliceContDiffOnProbe

variable {E C G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup C] [NormedSpace ℝ C]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Smoothness of a product-chart inverse on its target restricts to every
fixed-first-coordinate inverse slice. -/
theorem contDiffAt_inverseSlice_of_contDiffOn_symm
    (chart : OpenPartialHomeomorph E (C × G)) (n : WithTop ℕ∞)
    (hsymm : ContDiffOn ℝ n chart.symm chart.target)
    (r : C) (z : G) (hz : (r, z) ∈ chart.target) :
    ContDiffAt ℝ n (fun w : G => chart.symm (r, w)) z := by
  have hpair : ContDiffAt ℝ n (fun w : G => (r, w)) z :=
    contDiffAt_const.prodMk contDiffAt_id
  exact ((hsymm (r, z) hz).contDiffAt (chart.open_target.mem_nhds hz)).comp z hpair

#print axioms contDiffAt_inverseSlice_of_contDiffOn_symm

end SardProjectedChartInverseSliceContDiffOnProbe
