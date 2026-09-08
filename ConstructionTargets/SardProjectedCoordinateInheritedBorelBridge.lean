import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace

namespace SardProjectedCoordinateInheritedBorelBridgeProbe

theorem projectedCoordinates_inherited_borelSpace
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) :
    BorelSpace (LinearMap.range L.toLinearMap) ∧
      BorelSpace (LinearMap.range L.toLinearMap)ᗮ := by
  exact SardDerivativeRangeInheritedBorelSpaceProbe.range_orthogonal_inherited_borelSpace L

#print axioms projectedCoordinates_inherited_borelSpace

end SardProjectedCoordinateInheritedBorelBridgeProbe
