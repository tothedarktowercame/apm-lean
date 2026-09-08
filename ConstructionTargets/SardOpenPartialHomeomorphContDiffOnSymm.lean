import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace SardOpenPartialHomeomorphContDiffOnSymmProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A smooth open partial homeomorphism whose derivative is continuously
linearly invertible throughout its source has a smooth inverse on its target. -/
theorem contDiffOn_symm_of_forall_hasFDerivAt_equiv
    (chart : OpenPartialHomeomorph E F) (n : WithTop ℕ∞)
    (hchart : ContDiffOn ℝ n chart chart.source)
    (hderiv : ∀ x ∈ chart.source,
      ∃ D : E ≃L[ℝ] F, HasFDerivAt chart (D : E →L[ℝ] F) x) :
    ContDiffOn ℝ n chart.symm chart.target := by
  intro y hy
  have hx : chart.symm y ∈ chart.source := chart.symm.map_source hy
  obtain ⟨D, hD⟩ := hderiv (chart.symm y) hx
  have hsmooth : ContDiffAt ℝ n chart (chart.symm y) :=
    (hchart (chart.symm y) hx).contDiffAt (chart.open_source.mem_nhds hx)
  exact (chart.contDiffAt_symm hy hD hsmooth).contDiffWithinAt

#print axioms contDiffOn_symm_of_forall_hasFDerivAt_equiv

end SardOpenPartialHomeomorphContDiffOnSymmProbe
