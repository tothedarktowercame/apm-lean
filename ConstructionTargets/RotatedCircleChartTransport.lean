import ConstructionTargets.CircleRotationLocalization
open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.RotatedCircleChartTransport
open SingularHomologyConcrete SingularExcision
open ChartPairRelativeHomologyTransport ModelPairLocalHomologyOne
open OneDiskIncreasingOrientation OneDiskLocalOrientation
open LocalHomologyNeighborhoodExcision OneDimensionalChartLocalGenerator
open NestedOrientedChartCompatibility NestedOrientedChartCompatibility.PointedModelChart
open CircleActualLocalization CircleRotationLocalization

def rotatedChart (x : Circle) : PointedModelChart x where
  neighborhood := (Homeomorph.mulLeft x) '' (constructedChart (1 : Circle)).neighborhood
  open_neighborhood := (Homeomorph.mulLeft x).isOpenMap _ (constructedChart (1 : Circle)).open_neighborhood
  coordinates := (constructedChart (1 : Circle)).coordinates.trans
    ((Homeomorph.mulLeft x).image _)
  origin_eq := by
    change x * ((constructedChart (1 : Circle)).coordinates origin).1 = x
    rw [(constructedChart (1 : Circle)).origin_eq, mul_one]

theorem rotatedChart_ambient (x : Circle) :
    (rotatedChart x).ambient = (CircleRotationLocalization.rotation x).comp (constructedChart (1 : Circle)).ambient := rfl

theorem rotatedChart_chain_map (x : Circle) :
    relativeSingularMap P (deletedPoint x) (rotatedChart x).ambient (rotatedChart x).ambient_mapsTo =
      relativeSingularMap P (deletedPoint 1) (constructedChart (1 : Circle)).ambient
        (constructedChart (1 : Circle)).ambient_mapsTo ≫
      relativeSingularMap (deletedPoint 1) (deletedPoint x) (CircleRotationLocalization.rotation x) (rotation_mapsTo x) := by
  exact (relativeSingularMap_comp P (deletedPoint 1) (deletedPoint x)
    (constructedChart (1 : Circle)).ambient (CircleRotationLocalization.rotation x)
    (constructedChart (1 : Circle)).ambient_mapsTo (rotation_mapsTo x)
    (rotatedChart x).ambient_mapsTo).symm

theorem rotatedChart_localClass (x : Circle) :
    (rotatedChart x).localClass = rotatedLocalClass x := by
  unfold PointedModelChart.localClass
  rw [rotatedChart_chain_map, HomologicalComplex.homologyMap_comp]
  rfl

theorem globalClass_localizes_chart (x : Circle) :
    localization x globalClass = (rotatedChart x).localClass := by
  rw [rotatedChart_localClass]
  exact globalClass_localizes x

theorem rotatedChart_one_localClass :
    (rotatedChart (1 : Circle)).localClass = (constructedChart (1 : Circle)).localClass := by
  rw [← globalClass_localizes_chart]
  exact normalizedClass_localizes 1

theorem unique_global_chart_class :
    ∃! z : (SingularChains (TopCat.of Circle)).homology 1,
      (∀ w : (SingularChains (TopCat.of Circle)).homology 1, ∃ n : ℤ, n • z = w) ∧
      ∀ x : Circle, localization x z = (rotatedChart x).localClass := by
  refine ⟨globalClass, ⟨globalClass_generates, globalClass_localizes_chart⟩, ?_⟩
  intro z hz
  apply globalClass_unique
  exact (hz.2 1).trans rotatedChart_one_localClass

end ConstructionTargets.RotatedCircleChartTransport
#print axioms ConstructionTargets.RotatedCircleChartTransport.rotatedChart
#print axioms ConstructionTargets.RotatedCircleChartTransport.rotatedChart_ambient
#print axioms ConstructionTargets.RotatedCircleChartTransport.rotatedChart_chain_map
#print axioms ConstructionTargets.RotatedCircleChartTransport.rotatedChart_localClass
#print axioms ConstructionTargets.RotatedCircleChartTransport.globalClass_localizes_chart
#print axioms ConstructionTargets.RotatedCircleChartTransport.unique_global_chart_class
