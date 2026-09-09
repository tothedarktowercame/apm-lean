import ConstructionTargets.LocalHomologyNeighborhoodExcision
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Constructed one-dimensional charts and integral ambient local generators

A charted space modelled on EuclideanSpace ℝ (Fin 1) supplies the actual
boundaryless charts. Restrict an inverse chart to a selected ball and rescale
that ball from the model unit disk. Origin and deleted-point compatibility
are proved for this constructed map. T1 is required only for neighborhood
excision. All homology is production integral relative singular H1.

Concrete instances cover the Euclidean one-space, literal ℝ via its explicit
coordinate atlas, and Circle via its existing one-dimensional atlas.
No global fundamental class or overlap compatibility is asserted.
-/

open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.OneDimensionalChartLocalGenerator
open ConstructionTargets.SingularHomologyConcrete
open ConstructionTargets.SingularExcision
open ConstructionTargets.ChartPairRelativeHomologyTransport
open ConstructionTargets.ModelPairLocalHomologyOne
open ConstructionTargets.OneDiskIncreasingOrientation
open ConstructionTargets.OneDiskLocalOrientation
open ConstructionTargets.LocalHomologyNeighborhoodExcision

abbrev E := EuclideanSpace ℝ (Fin 1)
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

theorem exists_chart_radius (x : M) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (chartAt E x x) r ⊆ (chartAt E x).target :=
  Metric.isOpen_iff.mp (chartAt E x).open_target _ (mem_chart_target E x)

def chartRadius (x : M) : ℝ := (exists_chart_radius x).choose

theorem chartRadius_pos (x : M) : 0 < chartRadius x := (exists_chart_radius x).choose_spec.1

theorem chartRadius_ball_subset (x : M) :
    Metric.ball (chartAt E x x) (chartRadius x) ⊆ (chartAt E x).target :=
  (exists_chart_radius x).choose_spec.2

/-- Restrict the inverse of the actual chart at x to a ball about its coordinate. -/
def restrictedInverseChart (x : M) : OpenPartialHomeomorph E M :=
  (chartAt E x).symm.restr (Metric.ball (chartAt E x x) (chartRadius x))

def chartNeighborhood (x : M) : Set M := (restrictedInverseChart x).target

theorem restrictedInverseChart_source (x : M) :
    (restrictedInverseChart x).source = Metric.ball (chartAt E x x) (chartRadius x) := by
  rw [restrictedInverseChart, OpenPartialHomeomorph.restr_source' _ _ Metric.isOpen_ball]
  exact Set.inter_eq_right.mpr (chartRadius_ball_subset x)

theorem chartNeighborhood_open (x : M) : IsOpen (chartNeighborhood x) :=
  (restrictedInverseChart x).open_target

/-- Translate and scale the unit disk into the selected coordinate ball,
then apply the restricted inverse chart. -/
def modelChart (x : M) : D ≃ₜ chartNeighborhood x :=
  ((OpenPartialHomeomorph.unitBallBall (chartAt E x x) (chartRadius x)
      (chartRadius_pos x)).toHomeomorphSourceTarget.trans
    (Homeomorph.setCongr (restrictedInverseChart_source x).symm)).trans
      (restrictedInverseChart x).toHomeomorphSourceTarget

theorem modelChart_apply (x : M) (u : D) :
    (modelChart x u).1 = (chartAt E x).symm (chartRadius x • u.1 + chartAt E x x) := by
  rfl

theorem modelChart_origin (x : M) : (modelChart x origin).1 = x := by
  rw [modelChart_apply]
  change (chartAt E x).symm (chartRadius x • (0 : E) + chartAt E x x) = x
  rw [smul_zero, zero_add]
  exact (chartAt E x).left_inv (mem_chart_source E x)

theorem mem_chartNeighborhood (x : M) : x ∈ chartNeighborhood x := by
  have h := (modelChart x origin).2
  simpa only [modelChart_origin] using h

/-- The restricted chart identifies the deleted model origin with the deleted x. -/
theorem modelChart_deletedPoint_iff (x : M) (u : D) :
    u ∈ P ↔ modelChart x u ∈ neighborhoodDeletedPoint (chartNeighborhood x) x := by
  rw [mem_puncture_iff_ne_origin]
  change u ≠ origin ↔ (modelChart x u).1 ≠ x
  constructor
  · intro hu he
    apply hu
    apply (modelChart x).injective
    apply Subtype.ext
    exact he.trans (modelChart_origin x).symm
  · intro hu he
    exact hu ((congrArg (fun v => (modelChart x v).1) he).trans (modelChart_origin x))

/-- The ambient map built from the restricted chart and actual neighborhood inclusion. -/
def ambientChartMap (x : M) : C(D, M) :=
  (neighborhoodInclusion (chartNeighborhood x)).comp (pairContinuousMap (modelChart x))

theorem ambientChartMap_mapsTo (x : M) : Set.MapsTo (ambientChartMap x) P (deletedPoint x) :=
  (neighborhoodInclusion_mapsTo (chartNeighborhood x) x).comp
    (pairContinuousMap_mapsTo (modelChart x) P _ (modelChart_deletedPoint_iff x))

theorem ambientChartMap_chain_eq (x : M) :
    relativeSingularMap P (deletedPoint x) (ambientChartMap x) (ambientChartMap_mapsTo x) =
      relativeSingularMap P (neighborhoodDeletedPoint (chartNeighborhood x) x)
        (pairContinuousMap (modelChart x))
        (pairContinuousMap_mapsTo _ _ _ (modelChart_deletedPoint_iff x)) ≫
      relativeSingularMap (neighborhoodDeletedPoint (chartNeighborhood x) x) (deletedPoint x)
        (neighborhoodInclusion (chartNeighborhood x))
        (neighborhoodInclusion_mapsTo (chartNeighborhood x) x) := by
  symm
  exact relativeSingularMap_comp _ _ _ _ _ _ _ (ambientChartMap_mapsTo x)

theorem ambientChartMap_H1_isIso [T1Space M] (x : M) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap P (deletedPoint x) (ambientChartMap x) (ambientChartMap_mapsTo x)) 1) := by
  letI := relativeSingularMap_homeomorphPair_isIso (modelChart x) P
    (neighborhoodDeletedPoint (chartNeighborhood x) x) (modelChart_deletedPoint_iff x) 1
  letI := neighborhoodInclusion_H1_isIso (chartNeighborhood x) x
    (chartNeighborhood_open x) (mem_chartNeighborhood x)
  rw [ambientChartMap_chain_eq, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- The local class is the image under the actual chart-to-ambient map. -/
def ambientLocalGenerator (x : M) : (RelativeSingularChains (deletedPoint x)).homology 1 :=
  HomologicalComplex.homologyMap
    (relativeSingularMap P (deletedPoint x) (ambientChartMap x) (ambientChartMap_mapsTo x)) 1
    openDiskOnePunctureRelativeH1Generator

theorem ambientLocalGenerator_generates [T1Space M] (x : M) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 1,
      ∃ n : ℤ, n • ambientLocalGenerator x = z := by
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap P (deletedPoint x) (ambientChartMap x) (ambientChartMap_mapsTo x)) 1
  letI := ambientChartMap_H1_isIso x
  intro z
  let w := (asIso f).inv z
  refine ⟨openDiskOnePunctureRelativeH1IsoInt.hom w, ?_⟩
  change _ • f openDiskOnePunctureRelativeH1Generator = z
  rw [← map_zsmul, model_class_zsmul]
  exact ConcreteCategory.congr_hom (asIso f).inv_hom_id z

/-- Concrete Euclidean-line chart instance. -/
theorem euclideanLine_local_generator (x : E) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 1,
      ∃ n : ℤ, n • ambientLocalGenerator x = z := ambientLocalGenerator_generates x

/-- Concrete circle chart instance, using the existing one-dimensional circle atlas. -/
theorem circle_local_generator (x : Circle) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 1,
      ∃ n : ℤ, n • ambientLocalGenerator x = z := ambientLocalGenerator_generates x

/-- The ambient class is literally inclusion applied to chart-pair transport. -/
theorem ambientLocalGenerator_eq_inclusion_transport (x : M) :
    ambientLocalGenerator x =
      HomologicalComplex.homologyMap
        (relativeSingularMap (neighborhoodDeletedPoint (chartNeighborhood x) x) (deletedPoint x)
          (neighborhoodInclusion (chartNeighborhood x))
          (neighborhoodInclusion_mapsTo (chartNeighborhood x) x)) 1
        (transportedOpenDiskOnePunctureGenerator (modelChart x)
          (neighborhoodDeletedPoint (chartNeighborhood x) x) (modelChart_deletedPoint_iff x)) := by
  unfold ambientLocalGenerator
  rw [ambientChartMap_chain_eq, HomologicalComplex.homologyMap_comp]
  rfl

/-- Explicit real-line coordinate homeomorphism into the one-dimensional model. -/
def realLineCoordinates : ℝ ≃ₜ E where
  toFun t := WithLp.toLp 2 (fun _ : Fin 1 => t)
  invFun v := v 0
  left_inv _ := rfl
  right_inv v := by
    ext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  continuous_toFun := by fun_prop
  continuous_invFun := PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0

/-- The concrete one-chart atlas on the literal real line. -/
abbrev realLineAtlas : ChartedSpace E ℝ where
  atlas := {realLineCoordinates.toOpenPartialHomeomorph}
  chartAt _ := realLineCoordinates.toOpenPartialHomeomorph
  mem_chart_source _ := Set.mem_univ _
  chart_mem_atlas _ := Set.mem_singleton _

def realLocalGenerator (x : ℝ) : (RelativeSingularChains (deletedPoint x)).homology 1 :=
  letI := realLineAtlas
  ambientLocalGenerator x

theorem realLine_local_generator (x : ℝ) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 1,
      ∃ n : ℤ, n • realLocalGenerator x = z := by
  letI := realLineAtlas
  exact ambientLocalGenerator_generates x

end ConstructionTargets.OneDimensionalChartLocalGenerator
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.modelChart
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.modelChart_origin
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.modelChart_deletedPoint_iff
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap_chain_eq
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.ambientChartMap_H1_isIso
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.ambientLocalGenerator_generates
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.euclideanLine_local_generator
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.circle_local_generator

#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.ambientLocalGenerator_eq_inclusion_transport
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.realLineCoordinates
#print axioms ConstructionTargets.OneDimensionalChartLocalGenerator.realLine_local_generator
