import ConstructionTargets.SardImplicitFunctionDataSmoothChart
import ConstructionTargets.SardProjectedComplementedStrictDerivativeData
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

noncomputable section
namespace SardProjectedSmoothLocalRankChartProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A smooth map and its strict derivative determine a smooth projected
local-rank chart retaining the exact derivative-range coordinate formula. -/
theorem exists_projected_smooth_localRankChart
    (f : E → F) (x : E) (L : E →L[ℝ] F) (n : WithTop ℕ∞)
    (hn : n ≠ (↑(⊤ : ℕ∞) : WithTop ℕ∞))
    (hf : HasStrictFDerivAt f L x) (hfsmooth : ContDiffAt ℝ n f x) :
    ∃ e : OpenPartialHomeomorph E
        ((LinearMap.range L.toLinearMap) ×
          ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker),
      x ∈ e.source ∧
      (e : E →
        (LinearMap.range L.toLinearMap) ×
          ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker) =
        (fun y =>
          ((LinearMap.range L.toLinearMap).orthogonalProjection (f y),
            ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker.orthogonalProjection y)) ∧
      ContDiffOn ℝ n e e.source ∧ ContDiffOn ℝ n e.symm e.target := by
  let R := LinearMap.range L.toLinearMap
  letI hR : CompleteSpace R := by
    letI := L.toLinearMap.finiteDimensional_range
    exact R.complete_of_finiteDimensional.completeSpace_coe
  let A : E →L[ℝ] R := R.orthogonalProjection.comp L
  let G := A.ker
  letI hG : CompleteSpace G := by infer_instance
  let B : E →L[ℝ] G := G.orthogonalProjection
  have h := SardProjectedImplicitFunctionDataProbe.projected_complemented_strictDerivative_data
    f x L hf
  let φ := @ImplicitFunctionData.mk ℝ inferInstance E inferInstance inferInstance inferInstance
    R inferInstance inferInstance hR G inferInstance inferInstance hG
    (fun y => R.orthogonalProjection (f y)) A
    (fun y => G.orthogonalProjection y) B x h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2
  have hleft : ContDiffAt ℝ n (fun y => R.orthogonalProjection (f y)) x :=
    R.orthogonalProjection.contDiff.contDiffAt.comp x hfsmooth
  have hright : ContDiffAt ℝ n (fun y => G.orthogonalProjection y) x :=
    G.orthogonalProjection.contDiff.contDiffAt
  simpa [φ, ImplicitFunctionData.prodFun, R, A, G] using
    @SardImplicitFunctionDataSmoothChartProbe.exists_smooth_chart_restriction
      E R G inferInstance inferInstance inferInstance inferInstance inferInstance hR
      inferInstance inferInstance hG φ n hn hleft hright

#print axioms exists_projected_smooth_localRankChart

end SardProjectedSmoothLocalRankChartProbe
