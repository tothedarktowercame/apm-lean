import ConstructionTargets.SardFiniteOrderPointwiseRankChartNullityWitness
import ConstructionTargets.SardFiniteOrderProjectedSmoothChartTargetData
import ConstructionTargets.SardProjectedPositiveRankDimensionData
import ConstructionTargets.SardProjectedRankReducedDimensionIdentities
import ConstructionTargets.SardFiniteOrderProjectedChartOrthogonalResidualSliceZero
import ConstructionTargets.SardProjectedCoordinateExplicitInheritedMeasureData
import ConstructionTargets.SardFiniteOrderPositiveRankInstalledPointwiseData
import ConstructionTargets.SardFiniteOrderPositiveRankProjectedChartSliceData
import ConstructionTargets.SardFiniteOrderPointwiseWitnessExplicitMeasurableSpaces
import ConstructionTargets.SardProjectedCoordinateExplicitInheritedTopologyData
import ConstructionTargets.SardFiniteOrderPointwiseWitnessExplicitTopologyAndMeasureSpaces

open Set MeasureTheory

noncomputable section
namespace SardFiniteOrderPositiveRankPointwiseNullityProbe

universe u v

theorem exists_open_image_zero_of_finiteOrder_positiveRank
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F)
    (μF : Measure F) [Measure.IsAddHaarMeasure μF]
    (f : E → F) (x : E) (s U : Set E)
    (r order d : ℕ)
    (hs : IsClosed s) (hU : IsOpen U) (hxU : x ∈ U)
    (horder : order ≠ 0)
    (hstrict : HasStrictFDerivAt f L x)
    (hf : ContDiffOn ℝ order f univ)
    (hrank : Module.finrank ℝ (LinearMap.range L.toLinearMap) = r)
    (hrpos : 0 < r) (hnonsurj : ¬ Function.Surjective L)
    (hrankUpper : ∀ z ∈ U, Module.finrank ℝ
      (LinearMap.range (fderiv ℝ f z).toLinearMap) ≤ r)
    (hind : ∀ e : ℕ, e < d →
      SardClassicalFiniteOrderCriticalNullityPredicateProbe.ClassicalCriticalNullityAtDimension.{u,v} e)
    (hd : Module.finrank ℝ E ≤ d)
    (hadm : SardClassicalRegularityAdmissibilityProbe.SardOrderAdmissible
      (Module.finrank ℝ E) (Module.finrank ℝ F) order) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ μF (f '' (s ∩ V)) = 0 := by
  letI : @BorelSpace (LinearMap.range L.toLinearMap) inferInstance inferInstance :=
    (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).1
  letI : @BorelSpace (LinearMap.range L.toLinearMap)ᗮ inferInstance inferInstance :=
    (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).2
  let R := LinearMap.range L.toLinearMap
  let G := (R.orthogonalProjection.comp L).ker
  let S := Rᗮ
  obtain ⟨⟨hLCR⟩, ⟨hSCR⟩, ⟨hLCS⟩, ⟨hSCS⟩⟩ :=
    SardProjectedCoordinateExplicitInheritedTopologyDataProbe.exists_projectedCoordinates_explicit_inherited_topologyData L
  letI := hLCR
  letI := hSCR
  letI := hLCS
  letI := hSCS
  obtain ⟨chart, hxchart, hfirst, hsymm, hzero⟩ :=
    SardFiniteOrderPositiveRankProjectedChartSliceDataProbe.exists_finiteOrder_projectedChart_residualSliceZero
      f x L U r order hU hxU horder hstrict hf hrank hrankUpper
  obtain ⟨hsource, htarget⟩ :=
    SardProjectedRankReducedDimensionIdentitiesProbe.projected_rank_reduced_finranks L r hrank
  obtain ⟨⟨hrSource, hrTarget, hdrop⟩, hnontrivial, μR, μS, hμR, hμS⟩ :=
    SardFiniteOrderPositiveRankInstalledPointwiseDataProbe.exists_positiveRank_installed_pointwise_data
      L r hrank hrpos hnonsurj
  letI : Nontrivial S := hnontrivial
  letI : Measure.IsAddHaarMeasure μR := hμR
  letI : Measure.IsAddHaarMeasure μS := hμS
  let coord := SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates R
  let Q : F →L[ℝ] S := S.orthogonalProjection
  let P : S →L[ℝ] S := ContinuousLinearMap.id ℝ S
  apply SardFiniteOrderPointwiseWitnessExplicitTopologyAndMeasureSpacesProbe.exists_open_rankLocus_image_zero_explicit_topology_measureSpaces
    (C := R) (G := G) (S := S) (R := S)
    hLCR hSCR hLCS hSCS inferInstance inferInstance
    (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).1
    (SardProjectedCoordinateExplicitInheritedBorelDataProbe.projectedCoordinates_explicit_inherited_borelData L).2
    μF μR μS inferInstance hμR hμS
    chart coord f Q P s chart.source x hxchart hs chart.open_source
    (fun _ hz => hz) (by
      funext z
      exact (congrFun hfirst z).trans ((congrArg Prod.fst
        (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply
          R (f z))).symm))
  · intro y
    exact congrArg Prod.snd
      (SardTargetOrthogonalCoordinateEquivProbe.targetOrthogonalCoordinates_apply R y)
  · exact hind
  · exact lt_of_lt_of_le hdrop hd
  · exact hsource
  · exact htarget
  · exact horder
  · exact hsymm
  · exact hf.mono (fun _ _ => mem_univ _)
  · exact hadm
  · exact hrSource
  · exact hrTarget
  · exact Function.surjective_id
  · intro c z hcz
    simpa [P, Q, Function.comp_def, R, G, S] using hzero c z hcz

#print axioms exists_open_image_zero_of_finiteOrder_positiveRank

end SardFiniteOrderPositiveRankPointwiseNullityProbe
