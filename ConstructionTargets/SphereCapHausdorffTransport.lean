import ConstructionTargets.SphereCapEuclideanImage
import ConstructionTargets.SphereCapGraphDensity
import ConstructionTargets.C1GraphGlobalBounds

noncomputable section
namespace ConstructionTargets.SphereCapHausdorffTransport

open Set MeasureTheory
open SphereCapHeight SphereCapCoordinateIsometry SphereCapEuclideanImage
open ConstructionTargets.C1GraphMeasureDecomposition

lemma coordinate_hausdorff_image (d : ℕ) (s : Set (SphereCapL2Image.Ambient d)) :
    Measure.hausdorffMeasure (d : ℝ) (coordinateIsometry d '' s) =
      Measure.hausdorffMeasure (d : ℝ) s :=
  (coordinateIsometry d).toIsometryEquiv.hausdorffMeasure_image d s

lemma upper_strictCap_measure (d : ℕ) :
    Measure.hausdorffMeasure (d : ℝ) (strictUpperCap d) =
      ∫⁻ x in domain d, ENNReal.ofReal (1 / upper d x) ∂domainMeasure d := by
  rw [← image_upperGraph d, coordinate_hausdorff_image]
  rw [C1GraphGlobalBounds.exact_area_value d (upper d) (domain d)
    Metric.isOpen_ball (upper_contDiffOn d)]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_ball
  intro x hx
  have hd := SphereCapGraphDensity.fderiv_upper_density hx
  rw [C1GraphDensityControl.density_eq_sqrt] at hd
  simpa using congrArg ENNReal.ofReal hd

lemma lower_strictCap_measure (d : ℕ) :
    Measure.hausdorffMeasure (d : ℝ) (strictLowerCap d) =
      ∫⁻ x in domain d, ENNReal.ofReal (1 / upper d x) ∂domainMeasure d := by
  rw [← image_lowerGraph d, coordinate_hausdorff_image]
  rw [C1GraphGlobalBounds.exact_area_value d (lower d) (domain d)
    Metric.isOpen_ball (lower_contDiffOn d)]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_ball
  intro x hx
  have hd := SphereCapGraphDensity.fderiv_lower_density hx
  rw [C1GraphDensityControl.density_eq_sqrt] at hd
  simpa using congrArg ENNReal.ofReal hd

example : Measure.hausdorffMeasure (2 : ℝ) (strictUpperCap 2) =
    ∫⁻ x in domain 2, ENNReal.ofReal (1 / upper 2 x) ∂domainMeasure 2 :=
  upper_strictCap_measure 2
example : Measure.hausdorffMeasure (2 : ℝ) (strictLowerCap 2) =
    ∫⁻ x in domain 2, ENNReal.ofReal (1 / upper 2 x) ∂domainMeasure 2 :=
  lower_strictCap_measure 2
example : Measure.hausdorffMeasure (3 : ℝ) (strictUpperCap 3) =
    ∫⁻ x in domain 3, ENNReal.ofReal (1 / upper 3 x) ∂domainMeasure 3 :=
  upper_strictCap_measure 3
example : Measure.hausdorffMeasure (3 : ℝ) (strictLowerCap 3) =
    ∫⁻ x in domain 3, ENNReal.ofReal (1 / upper 3 x) ∂domainMeasure 3 :=
  lower_strictCap_measure 3

#print axioms coordinate_hausdorff_image
#print axioms upper_strictCap_measure
#print axioms lower_strictCap_measure

end ConstructionTargets.SphereCapHausdorffTransport
