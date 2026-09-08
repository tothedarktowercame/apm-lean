import ConstructionTargets.SardFiniteOrderProjectedInheritedMeasurePackage

open MeasureTheory

noncomputable section
namespace SardProjectedCoordinateExplicitInheritedMeasureDataProbe

theorem exists_projectedCoordinates_explicit_inherited_measureData
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L) :
    @BorelSpace (LinearMap.range L.toLinearMap) inferInstance inferInstance ∧
    @BorelSpace (LinearMap.range L.toLinearMap)ᗮ inferInstance inferInstance ∧
    Nontrivial (LinearMap.range L.toLinearMap)ᗮ ∧
      ∃ μR : @Measure (LinearMap.range L.toLinearMap) inferInstance,
      ∃ μS : @Measure (LinearMap.range L.toLinearMap)ᗮ inferInstance,
        @Measure.IsAddHaarMeasure (LinearMap.range L.toLinearMap)
          inferInstance inferInstance inferInstance μR ∧
        @Measure.IsAddHaarMeasure (LinearMap.range L.toLinearMap)ᗮ
          inferInstance inferInstance inferInstance μS := by
  obtain ⟨⟨hR, hS⟩, hn, μR, μS, hμR, hμS⟩ :=
    SardFiniteOrderProjectedInheritedMeasurePackageProbe.exists_projected_inherited_borel_addHaar_data L hL
  exact ⟨hR, hS, hn, μR, μS, hμR, hμS⟩

#print axioms exists_projectedCoordinates_explicit_inherited_measureData

end SardProjectedCoordinateExplicitInheritedMeasureDataProbe
