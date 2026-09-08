import ConstructionTargets.SardDerivativeRangeInheritedBorelAddHaarPackage
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace SardDerivativeRangeInheritedBorelSpaceProbe

/-- Closed finite-dimensional derivative-range coordinates inherit the Borel
measurable structure of the ambient target. -/
theorem range_orthogonal_inherited_borelSpace
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) :
    BorelSpace (LinearMap.range L.toLinearMap) ∧
      BorelSpace (LinearMap.range L.toLinearMap)ᗮ := by
  constructor
  · exact (MeasurableEmbedding.subtype_coe
      (LinearMap.range L.toLinearMap).closed_of_finiteDimensional.measurableSet).borelSpace
      Topology.IsInducing.subtypeVal
  · exact (MeasurableEmbedding.subtype_coe
      (LinearMap.range L.toLinearMap)ᗮ.closed_of_finiteDimensional.measurableSet).borelSpace
      Topology.IsInducing.subtypeVal

#print axioms range_orthogonal_inherited_borelSpace

end SardDerivativeRangeInheritedBorelSpaceProbe
