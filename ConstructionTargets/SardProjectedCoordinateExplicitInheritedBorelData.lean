import ConstructionTargets.SardDerivativeRangeInheritedBorelSpace

namespace SardProjectedCoordinateExplicitInheritedBorelDataProbe

theorem projectedCoordinates_explicit_inherited_borelData
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) :
    @BorelSpace (LinearMap.range L.toLinearMap) inferInstance inferInstance ∧
      @BorelSpace (LinearMap.range L.toLinearMap)ᗮ inferInstance inferInstance := by
  exact SardDerivativeRangeInheritedBorelSpaceProbe.range_orthogonal_inherited_borelSpace L

#print axioms projectedCoordinates_explicit_inherited_borelData

end SardProjectedCoordinateExplicitInheritedBorelDataProbe
