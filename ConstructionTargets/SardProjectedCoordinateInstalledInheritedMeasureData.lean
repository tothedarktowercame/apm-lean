import ConstructionTargets.SardProjectedCoordinateExplicitInheritedMeasureData
import ConstructionTargets.SardProjectedCoordinateExplicitInheritedBorelData

open MeasureTheory

noncomputable section
namespace SardProjectedCoordinateInstalledInheritedMeasureDataProbe

theorem exists_projectedCoordinates_installed_inherited_measureData
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) (hL : ¬ Function.Surjective L) :
    letI : BorelSpace (LinearMap.range L.toLinearMap) :=
      (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).1
    letI : BorelSpace (LinearMap.range L.toLinearMap)ᗮ :=
      (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).2
    Nontrivial (LinearMap.range L.toLinearMap)ᗮ ∧
      ∃ μR : Measure (LinearMap.range L.toLinearMap),
      ∃ μS : Measure (LinearMap.range L.toLinearMap)ᗮ,
        Measure.IsAddHaarMeasure μR ∧ Measure.IsAddHaarMeasure μS := by
  obtain ⟨_, _, hn, μR, μS, hμR, hμS⟩ :=
    SardProjectedCoordinateExplicitInheritedMeasureDataProbe.exists_projectedCoordinates_explicit_inherited_measureData L hL
  exact ⟨hn, μR, μS, hμR, hμS⟩

#print axioms exists_projectedCoordinates_installed_inherited_measureData

end SardProjectedCoordinateInstalledInheritedMeasureDataProbe
