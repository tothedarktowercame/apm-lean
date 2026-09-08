import ConstructionTargets.SardProjectedComplementedStrictDerivativeData

noncomputable section
namespace SardRangeProjectionCoordinateDerivativeProbe

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The derivative of the derivative-range coordinate is the range projection
composed with the ambient derivative. -/
theorem hasFDerivAt_rangeProjection_comp
    (f : E → F) (y : E) (D L : E →L[ℝ] F)
    (hf : HasFDerivAt f D y) :
    HasFDerivAt
      (fun z => (LinearMap.range L.toLinearMap).orthogonalProjection (f z))
      ((LinearMap.range L.toLinearMap).orthogonalProjection.comp D) y := by
  exact (LinearMap.range L.toLinearMap).orthogonalProjection.hasStrictFDerivAt.hasFDerivAt.comp y hf

#print axioms hasFDerivAt_rangeProjection_comp

end SardRangeProjectionCoordinateDerivativeProbe
