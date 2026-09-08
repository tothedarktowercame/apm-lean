import ConstructionTargets.SardProjectedPositiveRankDimensionData
import ConstructionTargets.SardFiniteOrderProjectedInheritedMeasurePackage

open MeasureTheory

noncomputable section
namespace SardFiniteOrderPositiveRankPointwiseDataProbe

theorem exists_positiveRank_dimension_inheritedMeasure_data
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) (r : ℕ)
    (hrank : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hrpos : 0 < r) (hnonsurj : ¬ Function.Surjective L) :
    (r ≤ Module.finrank ℝ E ∧ r ≤ Module.finrank ℝ F ∧
      Module.finrank ℝ
        ((LinearMap.range L.toLinearMap).orthogonalProjection.comp L).ker <
          Module.finrank ℝ E) ∧
    (BorelSpace (LinearMap.range L.toLinearMap) ∧
      BorelSpace (LinearMap.range L.toLinearMap)ᗮ) ∧
    Nontrivial (LinearMap.range L.toLinearMap)ᗮ ∧
      ∃ μR : Measure (LinearMap.range L.toLinearMap),
      ∃ μS : Measure (LinearMap.range L.toLinearMap)ᗮ,
        Measure.IsAddHaarMeasure μR ∧ Measure.IsAddHaarMeasure μS := by
  exact ⟨
    SardProjectedPositiveRankDimensionDataProbe.projected_positiveRank_dimension_data
      L r hrank hrpos,
    SardFiniteOrderProjectedInheritedMeasurePackageProbe.exists_projected_inherited_borel_addHaar_data
      L hnonsurj⟩

#print axioms exists_positiveRank_dimension_inheritedMeasure_data

end SardFiniteOrderPositiveRankPointwiseDataProbe
