import ConstructionTargets.SphereCapHausdorffTransport

noncomputable section
namespace ConstructionTargets.SphereCapC1GraphAreaComparison

open Set MeasureTheory
open SphereCapHeight SphereCapEuclideanImage SphereCapHausdorffTransport
open ConstructionTargets.C1GraphMeasureDecomposition

lemma subtype_measure (d : ℕ) (s : Set (EA d)) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure s) Set.univ =
      (Measure.hausdorffMeasure (d : ℝ) : Measure (EA d)) s := by
  have h := (isometry_subtype_coe : Isometry (Subtype.val : s → EA d)).hausdorffMeasure_image
    (Or.inl (Nat.cast_nonneg d)) Set.univ
  simpa using h.symm

lemma intrinsic_upper_strictCap_measure (d : ℕ) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (strictUpperCap d)) Set.univ =
      ∫⁻ x in domain d, ENNReal.ofReal (1 / upper d x) ∂domainMeasure d := by
  rw [subtype_measure, upper_strictCap_measure]

lemma intrinsic_lower_strictCap_measure (d : ℕ) :
    (Measure.hausdorffMeasure (d : ℝ) : Measure (strictLowerCap d)) Set.univ =
      ∫⁻ x in domain d, ENNReal.ofReal (1 / upper d x) ∂domainMeasure d := by
  rw [subtype_measure, lower_strictCap_measure]

example : (Measure.hausdorffMeasure (2 : ℝ) : Measure (strictUpperCap 2)) Set.univ =
    ∫⁻ x in domain 2, ENNReal.ofReal (1 / upper 2 x) ∂domainMeasure 2 :=
  intrinsic_upper_strictCap_measure 2
example : (Measure.hausdorffMeasure (2 : ℝ) : Measure (strictLowerCap 2)) Set.univ =
    ∫⁻ x in domain 2, ENNReal.ofReal (1 / upper 2 x) ∂domainMeasure 2 :=
  intrinsic_lower_strictCap_measure 2
example : (Measure.hausdorffMeasure (3 : ℝ) : Measure (strictUpperCap 3)) Set.univ =
    ∫⁻ x in domain 3, ENNReal.ofReal (1 / upper 3 x) ∂domainMeasure 3 :=
  intrinsic_upper_strictCap_measure 3
example : (Measure.hausdorffMeasure (3 : ℝ) : Measure (strictLowerCap 3)) Set.univ =
    ∫⁻ x in domain 3, ENNReal.ofReal (1 / upper 3 x) ∂domainMeasure 3 :=
  intrinsic_lower_strictCap_measure 3

#print axioms subtype_measure
#print axioms intrinsic_upper_strictCap_measure
#print axioms intrinsic_lower_strictCap_measure

end ConstructionTargets.SphereCapC1GraphAreaComparison
