import ConstructionTargets.CoefficientCompactBoundaryMotion
import ConstructionTargets.CoefficientOverlapRelative
noncomputable section
namespace ConstructionTargets.CoefficientChartBoundaryNeighborhood
open CategoryTheory PuncturedNormedSpaceRadialEquivalence CoefficientOverlapPair
variable (m : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+2))) M]
variable (a b x : M) (hx : x ∈ common m a b)
include hx in
theorem radius_exists : ∃ r : ℝ, 0 < r ∧ Metric.closedBall (0 : E m) r ⊆ image m a (common m a b) x := by
  obtain ⟨ε,hε,hs⟩ := Metric.isOpen_iff.mp (image_open m a (common m a b) x) 0 (left_image_zero m a b x hx)
  refine ⟨ε/2,by linarith,fun y hy => hs ?_⟩
  change dist y 0 < ε
  change dist y 0 ≤ ε/2 at hy
  exact lt_of_le_of_lt hy (by linarith)
def radius : ℝ := Classical.choose (radius_exists m a b x hx)
theorem radius_pos : 0 < radius m a b x hx := (Classical.choose_spec (radius_exists m a b x hx)).1
theorem radius_subset : Metric.closedBall (0 : E m) (radius m a b x hx) ⊆ image m a (common m a b) x :=
  (Classical.choose_spec (radius_exists m a b x hx)).2

def sphereBoundary : C(UnitSphere (E m), image m a (common m a b) x) where
  toFun z := ⟨radius m a b x hx • z.val, radius_subset m a b x hx (by
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [norm_smul, Real.norm_of_nonneg (radius_pos m a b x hx).le]
    have hz : ‖z.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using z.property
    rw [hz, mul_one])⟩
  continuous_toFun := by fun_prop

def mappedBoundary : C(UnitSphere (E m), E m) where
  toFun z := (transition m a b x (sphereBoundary m a b x hx z)).val
  continuous_toFun := continuous_subtype_val.comp ((transition m a b x).continuous.comp (sphereBoundary m a b x hx).continuous)
theorem mapped_avoids : ∀ z, mappedBoundary m a b x hx z ≠ 0 := by
  intro z
  apply CoefficientOverlapRelative.transition_mapsTo m a b x hx
  change radius m a b x hx • z.val ≠ 0
  apply smul_ne_zero (ne_of_gt (radius_pos m a b x hx))
  exact (unitSphereInclusion (E m) z).property

def sourceBoundary : C(UnitSphere (E m), M) :=
  (CoefficientOverlapPair.leftAmbient m a b x).comp (sphereBoundary m a b x hx)
theorem source_member (z : UnitSphere (E m)) : sourceBoundary m a b x hx z ∈ common m a b :=
  ((left m a b x).symm (sphereBoundary m a b x hx z)).property
theorem mapped_formula (z : UnitSphere (E m)) :
    mappedBoundary m a b x hx z = chartAt (E m) b (sourceBoundary m a b x hx z) - chartAt (E m) b x := rfl

variable (R : Type) [CommRing R]
theorem boundary_neighborhood : ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ common m a b ∧
    ∀ y ∈ V, ‖chartAt (E m) a y - chartAt (E m) a x‖ < radius m a b x hx ∧ ∃ hy : ∀ z, mappedBoundary m a b x hx z ≠ chartAt (E m) b y - chartAt (E m) b x,
      ∀ n : ℕ,
        (CoefficientRadialPair.F R n).map (TopCat.ofHom (CoefficientCompactBoundaryMotion.boundaryMap
          (mappedBoundary m a b x hx) 0 (mapped_avoids m a b x hx))) =
        (CoefficientRadialPair.F R n).map (TopCat.ofHom (CoefficientCompactBoundaryMotion.boundaryMap
          (mappedBoundary m a b x hx) (chartAt (E m) b y - chartAt (E m) b x) hy)) := by
  obtain ⟨δ,hδ,hmove⟩ := CoefficientCompactBoundaryMotion.local_homology_constancy R
    (mappedBoundary m a b x hx) 0 (mapped_avoids m a b x hx)
  let A := common m a b ∩ (fun y => ‖chartAt (E m) a y - chartAt (E m) a x‖) ⁻¹' Set.Iio (radius m a b x hx)
  let B := common m a b ∩ (fun y => ‖chartAt (E m) b y - chartAt (E m) b x‖) ⁻¹' Set.Iio δ
  have hopenA : IsOpen A :=
    (((chartAt (E m) a).continuousOn.mono Set.inter_subset_left).sub continuousOn_const).norm.isOpen_inter_preimage
      (common_open m a b) isOpen_Iio
  have hopenB : IsOpen B :=
    (((chartAt (E m) b).continuousOn.mono Set.inter_subset_right).sub continuousOn_const).norm.isOpen_inter_preimage
      (common_open m a b) isOpen_Iio
  refine ⟨A ∩ B,hopenA.inter hopenB,⟨⟨hx,by simpa using radius_pos m a b x hx⟩,⟨hx,by simpa using hδ⟩⟩,
    fun y hy => hy.1.1,fun y hy => ⟨hy.1.2,?_⟩⟩
  exact hmove (chartAt (E m) b y - chartAt (E m) b x) (by simpa using hy.2.2)

def integral_example (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := boundary_neighborhood m a b x hx ℤ
def rational_example (m : ℕ) (a b x : E m) (hx : x ∈ common m a b) := boundary_neighborhood m a b x hx ℚ
#print axioms radius_exists
#print axioms sphereBoundary
#print axioms mapped_avoids
#print axioms source_member
#print axioms mapped_formula
#print axioms boundary_neighborhood
#print axioms integral_example
#print axioms rational_example
end ConstructionTargets.CoefficientChartBoundaryNeighborhood
