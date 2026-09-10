import ConstructionTargets.LowerDimensionalSphereNullity
import ConstructionTargets.SphereEquatorImageNullity
import ConstructionTargets.HausdorffSubtypeNullity
import ConstructionTargets.SphereCapEquatorPartition
import ConstructionTargets.HausdorffBorelInstanceCoherence

noncomputable section
namespace ConstructionTargets.SphereEquatorHausdorffNullity
open MeasureTheory MeasureTheory.Measure Metric Set
open scoped MeasureTheory ENNReal

abbrev EA (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

theorem source_two_null :
    (μH[(2 : ℕ)] : Measure (ConstructionTargets.SphereEquatorImageNullity.E 2)) (sphere 0 1) = 0 := by
  rw [← ConstructionTargets.HausdorffBorelInstanceCoherence.hausdorffMeasure_apply_eq_of_borel
    _ _ _ _ (2 : ℕ) (sphere 0 1)]
  exact ConstructionTargets.LowerDimensionalSphereNullity.sphere_two_null

theorem source_three_null :
    (μH[(3 : ℕ)] : Measure (ConstructionTargets.SphereEquatorImageNullity.E 3)) (sphere 0 1) = 0 := by
  rw [← ConstructionTargets.HausdorffBorelInstanceCoherence.hausdorffMeasure_apply_eq_of_borel
    _ _ _ _ (3 : ℕ) (sphere 0 1)]
  exact ConstructionTargets.LowerDimensionalSphereNullity.sphere_three_null

theorem equator_two_ambient_null :
    (μH[(2 : ℕ)] : Measure (EA 2)) (ConstructionTargets.SphereEquatorImageNullity.equator 2) = 0 :=
  ConstructionTargets.SphereEquatorImageNullity.equator_measure_eq_zero 2 source_two_null

theorem equator_three_ambient_null :
    (μH[(3 : ℕ)] : Measure (EA 3)) (ConstructionTargets.SphereEquatorImageNullity.equator 3) = 0 :=
  ConstructionTargets.SphereEquatorImageNullity.equator_measure_eq_zero 3 source_three_null

theorem equator_two_intrinsic_null :
    (μH[(2 : ℕ)] : Measure (ConstructionTargets.SphereEquatorImageNullity.equator 2)) Set.univ = 0 := by
  exact ConstructionTargets.HausdorffSubtypeNullity.subtype_univ_null (d := (2 : ℕ)) (by norm_num)
    equator_two_ambient_null

theorem equator_three_intrinsic_null :
    (μH[(3 : ℕ)] : Measure (ConstructionTargets.SphereEquatorImageNullity.equator 3)) Set.univ = 0 := by
  exact ConstructionTargets.HausdorffSubtypeNullity.subtype_univ_null (d := (3 : ℕ)) (by norm_num)
    equator_three_ambient_null

theorem sphere_two_partition :
    sphere (0 : EA 2) 1 =
      ConstructionTargets.SphereCapEuclideanImage.strictUpperCap 2 ∪
      ConstructionTargets.SphereCapEuclideanImage.strictLowerCap 2 ∪
      ConstructionTargets.SphereEquatorImageNullity.equator 2 := by
  exact ConstructionTargets.SphereCapEquatorPartition.sphere_partition 2

theorem sphere_three_partition :
    sphere (0 : EA 3) 1 =
      ConstructionTargets.SphereCapEuclideanImage.strictUpperCap 3 ∪
      ConstructionTargets.SphereCapEuclideanImage.strictLowerCap 3 ∪
      ConstructionTargets.SphereEquatorImageNullity.equator 3 := by
  exact ConstructionTargets.SphereCapEquatorPartition.sphere_partition 3

#print axioms source_two_null
#print axioms source_three_null
#print axioms equator_two_ambient_null
#print axioms equator_three_ambient_null
#print axioms equator_two_intrinsic_null
#print axioms equator_three_intrinsic_null
#print axioms sphere_two_partition
#print axioms sphere_three_partition
end ConstructionTargets.SphereEquatorHausdorffNullity
