import ConstructionTargets.OneDimensionalChartLocalGenerator
import ConstructionTargets.HigherModelLocalHomology
open CategoryTheory
noncomputable section
set_option autoImplicit false
namespace ConstructionTargets.HigherChartLocalGenerator
open SingularHomologyConcrete SingularExcision ChartPairRelativeHomologyTransport
open LocalHomologyNeighborhoodExcision T02A06HemisphereExcision
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin (k+2))
abbrev D (k : ℕ) := euclideanOpenDisk (k+2)
abbrev P (k : ℕ) := puncturedOpenDiskSet (k+2)
def origin (k : ℕ) : D k := ⟨0, by simp [Metric.mem_ball]⟩
lemma mem_puncture_iff_ne_origin {k : ℕ} (u : D k) :
    u ∈ P k ↔ u ≠ origin k := by
  change u.val ≠ 0 ↔ u ≠ origin k
  simp only [ne_eq, Subtype.ext_iff, origin]

variable {k : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (E k) M]
theorem neighborhoodInclusion_Hn_isIso {X : Type} [TopologicalSpace X] [T1Space X] (k : ℕ)
    (U : Set X) (x : X) (hU : IsOpen U) (hx : x ∈ U) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint U x) (deletedPoint x)
        (neighborhoodInclusion U) (neighborhoodInclusion_mapsTo U x)) (k+2)) := by
  have hZ : Uᶜ ⊆ interior (deletedPoint x) := by
    have ho : IsOpen (deletedPoint x) := isClosed_singleton.isOpen_compl
    rw [ho.interior_eq]
    intro y hy hxy
    exact hy (hxy.symm ▸ hx)
  letI := relativeExcisionMap_homologyMap_isIso_add_two (deletedPoint x) Uᶜ hU.isClosed_compl hZ k
  letI := relativeSingularMap_homeomorphPair_isIso (neighborhoodExcisionHomeomorph U)
    (neighborhoodDeletedPoint U x) (excisedSubspace (deletedPoint x) Uᶜ)
    (neighborhoodExcision_pair_iff U x) (k+2)
  rw [neighborhoodInclusion_chain_eq, HomologicalComplex.homologyMap_comp]
  infer_instance

theorem exists_chart_radius (x : M) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (chartAt (E k) x x) r ⊆ (chartAt (E k) x).target :=
  Metric.isOpen_iff.mp (chartAt (E k) x).open_target _ (mem_chart_target (E k) x)

def chartRadius (x : M) : ℝ := (exists_chart_radius (k := k) x).choose

theorem chartRadius_pos (x : M) : 0 < chartRadius (k := k) x := (exists_chart_radius (k := k) x).choose_spec.1

theorem chartRadius_ball_subset (x : M) :
    Metric.ball (chartAt (E k) x x) (chartRadius (k := k) x) ⊆ (chartAt (E k) x).target :=
  (exists_chart_radius (k := k) x).choose_spec.2


def restrictedInverseChart (x : M) : OpenPartialHomeomorph (E k) M :=
  (chartAt (E k) x).symm.restr (Metric.ball (chartAt (E k) x x) (chartRadius (k := k) x))

def chartNeighborhood (x : M) : Set M := (restrictedInverseChart (k := k) x).target

theorem restrictedInverseChart_source (x : M) :
    (restrictedInverseChart (k := k) x).source = Metric.ball (chartAt (E k) x x) (chartRadius (k := k) x) := by
  rw [restrictedInverseChart, OpenPartialHomeomorph.restr_source' _ _ Metric.isOpen_ball]
  exact Set.inter_eq_right.mpr (chartRadius_ball_subset (k := k) x)

theorem chartNeighborhood_open (x : M) : IsOpen (chartNeighborhood (k := k) x) :=
  (restrictedInverseChart (k := k) x).open_target


def modelChart (x : M) : (D k) ≃ₜ chartNeighborhood (k := k) x :=
  ((OpenPartialHomeomorph.unitBallBall (chartAt (E k) x x) (chartRadius (k := k) x)
      (chartRadius_pos (k := k) x)).toHomeomorphSourceTarget.trans
    (Homeomorph.setCongr (restrictedInverseChart_source (k := k) x).symm)).trans
      (restrictedInverseChart (k := k) x).toHomeomorphSourceTarget

theorem modelChart_apply (x : M) (u : (D k)) :
    (modelChart (k := k) x u).1 = (chartAt (E k) x).symm (chartRadius (k := k) x • u.1 + chartAt (E k) x x) := by
  rfl

theorem modelChart_origin (x : M) : (modelChart (k := k) x (origin k)).1 = x := by
  rw [modelChart_apply (k := k)]
  change (chartAt (E k) x).symm (chartRadius (k := k) x • (0 : (E k)) + chartAt (E k) x x) = x
  rw [smul_zero, zero_add]
  exact (chartAt (E k) x).left_inv (mem_chart_source (E k) x)

theorem mem_chartNeighborhood (x : M) : x ∈ chartNeighborhood (k := k) x := by
  have h := (modelChart (k := k) x (origin k)).2
  simpa only [modelChart_origin (k := k)] using h


theorem modelChart_deletedPoint_iff (x : M) (u : (D k)) :
    u ∈ (P k) ↔ modelChart (k := k) x u ∈ neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x := by
  rw [mem_puncture_iff_ne_origin]
  change u ≠ (origin k) ↔ (modelChart (k := k) x u).1 ≠ x
  constructor
  · intro hu he
    apply hu
    apply (modelChart (k := k) x).injective
    apply Subtype.ext
    exact he.trans (modelChart_origin (k := k) x).symm
  · intro hu he
    exact hu ((congrArg (fun v => (modelChart (k := k) x v).1) he).trans (modelChart_origin (k := k) x))


def ambientChartMap (x : M) : C((D k), M) :=
  (neighborhoodInclusion (chartNeighborhood (k := k) x)).comp (pairContinuousMap (modelChart (k := k) x))

theorem ambientChartMap_mapsTo (x : M) : Set.MapsTo (ambientChartMap (k := k) x) (P k) (deletedPoint x) :=
  (neighborhoodInclusion_mapsTo (chartNeighborhood (k := k) x) x).comp
    (pairContinuousMap_mapsTo (modelChart (k := k) x) (P k) _ (modelChart_deletedPoint_iff (k := k) x))

theorem ambientChartMap_chain_eq (x : M) :
    relativeSingularMap (P k) (deletedPoint x) (ambientChartMap (k := k) x) (ambientChartMap_mapsTo (k := k) x) =
      relativeSingularMap (P k) (neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x)
        (pairContinuousMap (modelChart (k := k) x))
        (pairContinuousMap_mapsTo _ _ _ (modelChart_deletedPoint_iff (k := k) x)) ≫
      relativeSingularMap (neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x) (deletedPoint x)
        (neighborhoodInclusion (chartNeighborhood (k := k) x))
        (neighborhoodInclusion_mapsTo (chartNeighborhood (k := k) x) x) := by
  symm
  exact relativeSingularMap_comp _ _ _ _ _ _ _ (ambientChartMap_mapsTo (k := k) x)

theorem ambientChartMap_Hn_isIso [T1Space M] (x : M) :
    IsIso (HomologicalComplex.homologyMap
      (relativeSingularMap (P k) (deletedPoint x) (ambientChartMap (k := k) x) (ambientChartMap_mapsTo (k := k) x)) (k+2)) := by
  letI := relativeSingularMap_homeomorphPair_isIso (modelChart (k := k) x) (P k)
    (neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x) (modelChart_deletedPoint_iff (k := k) x) (k+2)
  letI := neighborhoodInclusion_Hn_isIso k (chartNeighborhood (k := k) x) x
    (chartNeighborhood_open (k := k) x) (mem_chartNeighborhood (k := k) x)
  rw [ambientChartMap_chain_eq (k := k), HomologicalComplex.homologyMap_comp]
  infer_instance


def ambientLocalGenerator (x : M) : (RelativeSingularChains (deletedPoint x)).homology (k+2) :=
  HomologicalComplex.homologyMap
    (relativeSingularMap (P k) (deletedPoint x) (ambientChartMap (k := k) x) (ambientChartMap_mapsTo (k := k) x)) (k+2)
    (HigherModelLocalHomology.generator k)

theorem ambientLocalGenerator_generates [T1Space M] (x : M) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology (k+2),
      ∃ n : ℤ, n • ambientLocalGenerator (k := k) x = z := by
  let f := HomologicalComplex.homologyMap
    (relativeSingularMap (P k) (deletedPoint x) (ambientChartMap (k := k) x) (ambientChartMap_mapsTo (k := k) x)) (k+2)
  letI := ambientChartMap_Hn_isIso (k := k) x
  intro z
  let w := (asIso f).inv z
  obtain ⟨m, hm⟩ := HigherModelLocalHomology.generates k w
  refine ⟨m, ?_⟩
  change m • f (HigherModelLocalHomology.generator k) = z
  rw [← map_zsmul, hm]
  exact ConcreteCategory.congr_hom (asIso f).inv_hom_id z

theorem ambientChartMap_excision_chain_eq (x : M) :
    relativeSingularMap (P k) (deletedPoint x) (ambientChartMap (k := k) x)
      (ambientChartMap_mapsTo (k := k) x) =
    relativeSingularMap (P k) (neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x)
      (pairContinuousMap (modelChart (k := k) x))
      (pairContinuousMap_mapsTo _ _ _ (modelChart_deletedPoint_iff (k := k) x)) ≫
    relativeSingularMap (neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x)
      (excisedSubspace (deletedPoint x) (chartNeighborhood (k := k) x)ᶜ)
      (pairContinuousMap (neighborhoodExcisionHomeomorph (chartNeighborhood (k := k) x)))
      (pairContinuousMap_mapsTo _ _ _
        (neighborhoodExcision_pair_iff (chartNeighborhood (k := k) x) x)) ≫
    relativeExcisionMap (deletedPoint x) (chartNeighborhood (k := k) x)ᶜ := by
  rw [ambientChartMap_chain_eq, neighborhoodInclusion_chain_eq]

theorem ambientLocalGenerator_eq_inclusion_transport (x : M) :
    ambientLocalGenerator (k := k) x =
    HomologicalComplex.homologyMap
      (relativeSingularMap (neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x)
        (deletedPoint x) (neighborhoodInclusion (chartNeighborhood (k := k) x))
        (neighborhoodInclusion_mapsTo (chartNeighborhood (k := k) x) x)) (k+2)
      (HomologicalComplex.homologyMap
        (relativeSingularMap (P k) (neighborhoodDeletedPoint (chartNeighborhood (k := k) x) x)
          (pairContinuousMap (modelChart (k := k) x))
          (pairContinuousMap_mapsTo _ _ _ (modelChart_deletedPoint_iff (k := k) x))) (k+2)
        (HigherModelLocalHomology.generator k)) := by
  unfold ambientLocalGenerator
  rw [ambientChartMap_chain_eq, HomologicalComplex.homologyMap_comp]
  rfl

theorem dimension_two_local_generator (x : E 0) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 2,
      ∃ m : ℤ, m • ambientLocalGenerator (k := 0) x = z :=
  ambientLocalGenerator_generates (k := 0) x

theorem dimension_four_local_generator (x : E 2) :
    ∀ z : (RelativeSingularChains (deletedPoint x)).homology 4,
      ∃ m : ℤ, m • ambientLocalGenerator (k := 2) x = z :=
  ambientLocalGenerator_generates (k := 2) x
end ConstructionTargets.HigherChartLocalGenerator

#print axioms ConstructionTargets.HigherChartLocalGenerator.modelChart
#print axioms ConstructionTargets.HigherChartLocalGenerator.modelChart_origin
#print axioms ConstructionTargets.HigherChartLocalGenerator.modelChart_deletedPoint_iff
#print axioms ConstructionTargets.HigherChartLocalGenerator.ambientChartMap_excision_chain_eq
#print axioms ConstructionTargets.HigherChartLocalGenerator.ambientChartMap_Hn_isIso
#print axioms ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_generates
#print axioms ConstructionTargets.HigherChartLocalGenerator.ambientLocalGenerator_eq_inclusion_transport
#print axioms ConstructionTargets.HigherChartLocalGenerator.dimension_two_local_generator
#print axioms ConstructionTargets.HigherChartLocalGenerator.dimension_four_local_generator
