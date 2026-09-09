import ConstructionTargets.OneDimensionalChartLocalGenerator

open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.NestedOrientedChartCompatibility
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.ChartPairRelativeHomologyTransport
open ConstructionTargets.ModelPairLocalHomologyOne
open ConstructionTargets.OneDiskIncreasingOrientation
open ConstructionTargets.OneDiskLocalOrientation
open ConstructionTargets.LocalHomologyNeighborhoodExcision
open ConstructionTargets.OneDimensionalChartLocalGenerator

variable {M : Type} [TopologicalSpace M]

/-- Pointed neighborhood coordinates, containing only geometric data. -/
structure PointedModelChart (x : M) where
  neighborhood : Set M
  open_neighborhood : IsOpen neighborhood
  coordinates : D ≃ₜ neighborhood
  origin_eq : (coordinates origin).1 = x

namespace PointedModelChart
variable {x : M}

def ambient (c : PointedModelChart x) : C(D, M) :=
  (neighborhoodInclusion c.neighborhood).comp (pairContinuousMap c.coordinates)

theorem puncture_iff (c : PointedModelChart x) (u : D) :
    u ∈ P ↔ c.coordinates u ∈ neighborhoodDeletedPoint c.neighborhood x := by
  rw [mem_puncture_iff_ne_origin]
  change u ≠ origin ↔ (c.coordinates u).1 ≠ x
  constructor
  · intro hu he
    apply hu
    apply c.coordinates.injective
    exact Subtype.ext (he.trans c.origin_eq.symm)
  · intro hu he
    exact hu ((congrArg (fun v => (c.coordinates v).1) he).trans c.origin_eq)

theorem ambient_mapsTo (c : PointedModelChart x) : Set.MapsTo c.ambient P (deletedPoint x) :=
  (neighborhoodInclusion_mapsTo c.neighborhood x).comp
    (pairContinuousMap_mapsTo c.coordinates P _ c.puncture_iff)

def localClass (c : PointedModelChart x) : (RelativeSingularChains (deletedPoint x)).homology 1 :=
  HomologicalComplex.homologyMap
    (relativeSingularMap P (deletedPoint x) c.ambient c.ambient_mapsTo) 1
    openDiskOnePunctureRelativeH1Generator

/-- The actual coordinate transition for nested neighborhoods. -/
def transition (c d : PointedModelChart x) (h : c.neighborhood ⊆ d.neighborhood) : C(D,D) :=
  (pairContinuousMap d.coordinates.symm).comp
    ((⟨fun u : c.neighborhood => (⟨u.1, h u.2⟩ : d.neighborhood), by fun_prop⟩ :
      C(c.neighborhood, d.neighborhood)).comp (pairContinuousMap c.coordinates))

theorem transition_origin (c d : PointedModelChart x) (h : c.neighborhood ⊆ d.neighborhood) :
    transition c d h origin = origin := by
  apply d.coordinates.injective
  change d.coordinates (d.coordinates.symm _) = d.coordinates origin
  rw [d.coordinates.apply_symm_apply]
  exact Subtype.ext (c.origin_eq.trans d.origin_eq.symm)

theorem ambient_transition (c d : PointedModelChart x) (h : c.neighborhood ⊆ d.neighborhood) :
    d.ambient.comp (transition c d h) = c.ambient := by
  apply ContinuousMap.ext
  intro u
  change (d.coordinates (d.coordinates.symm _)).1 = (c.coordinates u).1
  rw [d.coordinates.apply_symm_apply]
  rfl

/-- Nested charts are compatible when the constructed coordinate transition
is increasing. This asserts no equality or sign of homology maps. -/
def Compatible (c d : PointedModelChart x) (h : c.neighborhood ⊆ d.neighborhood) : Prop :=
  Increasing (transition c d h)

/-- Naturality through the actual nested transition, before evaluating any class. -/
theorem transition_homology_square (c d : PointedModelChart x)
    (h : c.neighborhood ⊆ d.neighborhood) (hc : Compatible c d h) :
    HomologicalComplex.homologyMap
      (relativeSingularMap P P (transition c d h)
        (increasing_mapsTo _ hc (transition_origin c d h))) 1 ≫
      HomologicalComplex.homologyMap
        (relativeSingularMap P (deletedPoint x) d.ambient d.ambient_mapsTo) 1 =
    HomologicalComplex.homologyMap
      (relativeSingularMap P (deletedPoint x) c.ambient c.ambient_mapsTo) 1 := by
  have hs := relativeSingularHomologyMap_comp P P (deletedPoint x)
    (transition c d h) d.ambient
    (increasing_mapsTo _ hc (transition_origin c d h)) d.ambient_mapsTo
    (d.ambient_mapsTo.comp (increasing_mapsTo _ hc (transition_origin c d h))) 1
  simpa only [ambient_transition] using hs

/-- Compatible nested charts determine equal classes in the same ambient
local H1 group, using the geometric increasing-map computation. -/
theorem compatible_localClass_eq (c d : PointedModelChart x)
    (h : c.neighborhood ⊆ d.neighborhood) (hc : Compatible c d h) :
    c.localClass = d.localClass := by
  have hs := ConcreteCategory.congr_hom (transition_homology_square c d h hc)
    openDiskOnePunctureRelativeH1Generator
  change HomologicalComplex.homologyMap
    (relativeSingularMap P (deletedPoint x) d.ambient d.ambient_mapsTo) 1
    (HomologicalComplex.homologyMap
      (relativeSingularMap P P (transition c d h)
        (increasing_mapsTo _ hc (transition_origin c d h))) 1
      openDiskOnePunctureRelativeH1Generator) = c.localClass at hs
  rw [modelGenerator_map_of_increasing _ hc (transition_origin c d h)] at hs
  exact hs.symm

/-- The local class attached to geometric chart data is a generator, by excision. -/
theorem localClass_generates [T1Space M] (c : PointedModelChart x) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 1,
      ∃ n : ℤ, n • c.localClass = z := by
  have hx : x ∈ c.neighborhood := by
    have h := (c.coordinates origin).2
    simpa only [c.origin_eq] using h
  let e := relativeSingularHomologyIsoOfHomeomorphPair c.coordinates P
    (neighborhoodDeletedPoint c.neighborhood x) c.puncture_iff 1
  have hg : ∀ z : (RelativeSingularChains (neighborhoodDeletedPoint c.neighborhood x)).homology 1,
      ∃ n : ℤ, n • e.hom openDiskOnePunctureRelativeH1Generator = z := by
    intro z
    refine ⟨openDiskOnePunctureRelativeH1IsoInt.hom (e.inv z), ?_⟩
    rw [← map_zsmul, model_class_zsmul]
    exact ConcreteCategory.congr_hom e.inv_hom_id z
  have h := neighborhoodInclusion_sends_generator c.neighborhood x c.open_neighborhood hx
    (e.hom openDiskOnePunctureRelativeH1Generator) hg
  have hc := relativeSingularHomologyMap_comp P
    (neighborhoodDeletedPoint c.neighborhood x) (deletedPoint x)
    (pairContinuousMap c.coordinates) (neighborhoodInclusion c.neighborhood)
    (pairContinuousMap_mapsTo c.coordinates P _ c.puncture_iff)
    (neighborhoodInclusion_mapsTo c.neighborhood x) c.ambient_mapsTo 1
  have he := ConcreteCategory.congr_hom hc openDiskOnePunctureRelativeH1Generator
  change HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint c.neighborhood x) (deletedPoint x)
        (neighborhoodInclusion c.neighborhood) (neighborhoodInclusion_mapsTo c.neighborhood x)) 1
      (e.hom openDiskOnePunctureRelativeH1Generator) = c.localClass at he
  simpa only [he] using h

end PointedModelChart

/-- The banked restricted chart supplies this geometric data without an extra hypothesis. -/
def constructedChart [ChartedSpace E M] (x : M) : PointedModelChart x where
  neighborhood := chartNeighborhood x
  open_neighborhood := chartNeighborhood_open x
  coordinates := modelChart x
  origin_eq := modelChart_origin x

theorem constructedChart_localClass [ChartedSpace E M] (x : M) :
    (constructedChart x).localClass = ambientLocalGenerator x := rfl

/-- A common nested chart with increasing transitions suffices for overlap
compatibility; constructing that common restriction remains a separate step. -/
theorem localClass_eq_of_common_nested_chart {x : M}
    (c d common : PointedModelChart x)
    (hc : common.neighborhood ⊆ c.neighborhood)
    (hd : common.neighborhood ⊆ d.neighborhood)
    (hinc : PointedModelChart.Compatible common c hc)
    (hinc' : PointedModelChart.Compatible common d hd) :
    c.localClass = d.localClass :=
  (PointedModelChart.compatible_localClass_eq common c hc hinc).symm.trans
    (PointedModelChart.compatible_localClass_eq common d hd hinc')

end ConstructionTargets.NestedOrientedChartCompatibility
#print axioms ConstructionTargets.NestedOrientedChartCompatibility.PointedModelChart.transition
#print axioms ConstructionTargets.NestedOrientedChartCompatibility.PointedModelChart.ambient_transition
#print axioms ConstructionTargets.NestedOrientedChartCompatibility.PointedModelChart.transition_homology_square
#print axioms ConstructionTargets.NestedOrientedChartCompatibility.PointedModelChart.compatible_localClass_eq
#print axioms ConstructionTargets.NestedOrientedChartCompatibility.constructedChart_localClass
#print axioms ConstructionTargets.NestedOrientedChartCompatibility.localClass_eq_of_common_nested_chart

#print axioms ConstructionTargets.NestedOrientedChartCompatibility.PointedModelChart.localClass_generates
