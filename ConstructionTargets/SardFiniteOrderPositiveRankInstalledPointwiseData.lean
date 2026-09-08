import ConstructionTargets.SardProjectedCoordinateInstalledInheritedMeasureData
import ConstructionTargets.SardProjectedPositiveRankDimensionData

open MeasureTheory

noncomputable section
namespace SardFiniteOrderPositiveRankInstalledPointwiseDataProbe

theorem exists_positiveRank_installed_pointwise_data
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) (r : ℕ)
    (hrank : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hrpos : 0 < r) (hL : ¬ Function.Surjective L) :
    letI : BorelSpace (LinearMap.range L.toLinearMap) :=
      (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).1
    letI : BorelSpace (LinearMap.range L.toLinearMap)ᗮ :=
      (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).2
    (r ≤ Module.finrank ℝ E ∧ r ≤ Module.finrank ℝ F ∧
      Module.finrank ℝ
        ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker <
          Module.finrank ℝ E) ∧
    Nontrivial (LinearMap.range L.toLinearMap)ᗮ ∧
      ∃ μR : Measure (LinearMap.range L.toLinearMap),
      ∃ μS : Measure (LinearMap.range L.toLinearMap)ᗮ,
        Measure.IsAddHaarMeasure μR ∧ Measure.IsAddHaarMeasure μS := by
  exact ⟨
    SardProjectedPositiveRankDimensionDataProbe.projected_positiveRank_dimension_data
      L r hrank hrpos,
    SardProjectedCoordinateInstalledInheritedMeasureDataProbe.exists_projectedCoordinates_installed_inherited_measureData
      L hL⟩

#print axioms exists_positiveRank_installed_pointwise_data

end SardFiniteOrderPositiveRankInstalledPointwiseDataProbe
