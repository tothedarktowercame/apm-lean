import ConstructionTargets.SphereEquatorHausdorffNullity
import ConstructionTargets.SphereCapC1GraphAreaComparison

noncomputable section
namespace ConstructionTargets.SphereCapNullEquatorMeasureAssembly

open Metric Set MeasureTheory
open SphereCapHeight SphereCapEuclideanImage SphereCapHausdorffTransport
open SphereCapEquatorPartition SphereEquatorImageNullity
open ConstructionTargets.C1GraphMeasureDecomposition

abbrev EA (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

theorem sphere_measure (d : ℕ)
    (hnull : (Measure.hausdorffMeasure (d : ℝ) : Measure (EA d)) (SphereCapEquatorPartition.equator d) = 0) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (EA d)) (sphere 0 1) =
      (∫⁻ x in domain d, ENNReal.ofReal (1 / upper d x) ∂domainMeasure d) +
      (∫⁻ x in domain d, ENNReal.ofReal (1 / upper d x) ∂domainMeasure d) := by
  rw [sphere_partition]
  rw [measure_union
    ((disjoint_upper_equator d).union_left (disjoint_lower_equator d))
    (measurable_equator d)]
  rw [measure_union (disjoint_upper_lower d) (measurable_strictLowerCap d)]
  rw [hnull, add_zero, upper_strictCap_measure, lower_strictCap_measure]

theorem sphere_two_measure :
    (Measure.hausdorffMeasure (2 : ℝ) : Measure (EA 2)) (sphere 0 1) =
      (∫⁻ x in domain 2, ENNReal.ofReal (1 / upper 2 x) ∂domainMeasure 2) +
      (∫⁻ x in domain 2, ENNReal.ofReal (1 / upper 2 x) ∂domainMeasure 2) :=
  sphere_measure 2 SphereEquatorHausdorffNullity.equator_two_ambient_null

theorem sphere_three_measure :
    (Measure.hausdorffMeasure (3 : ℝ) : Measure (EA 3)) (sphere 0 1) =
      (∫⁻ x in domain 3, ENNReal.ofReal (1 / upper 3 x) ∂domainMeasure 3) +
      (∫⁻ x in domain 3, ENNReal.ofReal (1 / upper 3 x) ∂domainMeasure 3) :=
  sphere_measure 3 SphereEquatorHausdorffNullity.equator_three_ambient_null

#print axioms sphere_measure
#print axioms sphere_two_measure
#print axioms sphere_three_measure

end ConstructionTargets.SphereCapNullEquatorMeasureAssembly
