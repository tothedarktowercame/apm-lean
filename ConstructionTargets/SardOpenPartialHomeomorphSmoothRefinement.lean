import ConstructionTargets.SardOpenPartialHomeomorphContDiffOnSymm

namespace SardOpenPartialHomeomorphSmoothRefinementProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A regular base point of an open partial homeomorphism admits a restriction
that retains the chart function and is smooth in both directions. -/
theorem exists_smooth_restriction_at
    (chart : OpenPartialHomeomorph E F) (n : WithTop ℕ∞)
    (hn : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (x : E) (hx : x ∈ chart.source)
    (D : E ≃L[ℝ] F) (hD : HasFDerivAt chart (D : E →L[ℝ] F) x)
    (hsmooth : ContDiffAt ℝ n chart x) :
    ∃ e : OpenPartialHomeomorph E F,
      x ∈ e.source ∧ (e : E → F) = chart ∧
      ContDiffOn ℝ n e e.source ∧ ContDiffOn ℝ n e.symm e.target := by
  let e := chart.restrContDiff ℝ n hn
  have hD' : HasFDerivAt chart (D : E →L[ℝ] F) (chart.symm (chart x)) := by
    simpa [chart.left_inv hx] using hD
  have hsmooth' : ContDiffAt ℝ n chart (chart.symm (chart x)) := by
    simpa [chart.left_inv hx] using hsmooth
  have hinv : ContDiffAt ℝ n chart.symm (chart x) :=
    chart.contDiffAt_symm (chart.map_source hx) hD' hsmooth'
  have hxe : x ∈ e.source := by
    exact ⟨hx, hsmooth, by simpa [chart.left_inv hx] using hinv⟩
  refine ⟨e, hxe, ?_,
    OpenPartialHomeomorph.contDiffOn_restrContDiff_source (𝕜 := ℝ) chart hn,
    OpenPartialHomeomorph.contDiffOn_restrContDiff_target (𝕜 := ℝ) chart hn⟩
  ext y
  rfl

#print axioms exists_smooth_restriction_at

end SardOpenPartialHomeomorphSmoothRefinementProbe
