import ConstructionTargets.C1GraphPartition
import ConstructionTargets.C1GraphDensityControl

noncomputable section
namespace ConstructionTargets.C1GraphMeasureDecomposition

open Set MeasureTheory
open scoped ENNReal Function
open ConstructionTargets.LinearGraphMeasure
open ConstructionTargets.C1GraphPartition

abbrev domainMeasure (d : ℕ) : Measure (E d) :=
  Measure.hausdorffMeasure (d : ℝ)

abbrev ambientMeasure (d : ℕ) : Measure (Ambient d) :=
  Measure.hausdorffMeasure (d : ℝ)

def densityAt (d : ℕ) (f : E d → ℝ) (x : E d) : ℝ≥0∞ :=
  ENNReal.ofReal (C1GraphDensityControl.density (fderiv ℝ f x))

theorem densityAt_value (d : ℕ) (f : E d → ℝ) (x : E d) :
    densityAt d f x = ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ f x‖ ^ 2)) := by
  rw [densityAt, C1GraphDensityControl.density_eq_sqrt]

theorem densityAt_continuousOn (d : ℕ) (f : E d → ℝ) (U : Set (E d))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ContinuousOn (densityAt d f) U := by
  have hd : ContinuousOn (fderiv ℝ f) U :=
    hf.continuousOn_fderiv_of_isOpen hU (by norm_num)
  exact C1GraphDensityControl.continuous_ennrealDensity.continuousOn.comp hd
    (fun _ _ => Set.mem_univ _)

variable (d : ℕ) (f : E d → ℝ) (U : Set (E d))
variable (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (ε : ℝ) (hε : 0 < ε)

theorem graph_measure_sum :
    ambientMeasure d (GraphMetricComparison.Graph d f U) =
      ∑' n, ambientMeasure d
        (GraphMetricComparison.Graph d f (pieces d f U hU hf ε hε n)) := by
  rw [← images_union d f U hU hf ε hε]
  exact measure_iUnion (images_disjoint d f U hU hf ε hε)
    (images_measurable d f U hU hf ε hε)

theorem density_integral_sum :
    ∫⁻ x in U, densityAt d f x ∂domainMeasure d =
      ∑' n, ∫⁻ x in pieces d f U hU hf ε hε n,
        densityAt d f x ∂domainMeasure d := by
  calc
    _ = ∫⁻ x in (⋃ n, pieces d f U hU hf ε hε n),
        densityAt d f x ∂domainMeasure d := by
      congr 1
      exact congrArg (Measure.restrict (domainMeasure d))
        (pieces_union d f U hU hf ε hε).symm
    _ = _ := lintegral_iUnion (pieces_measurable d f U hU hf ε hε)
      (pieces_disjoint d f U hU hf ε hε) _

theorem selected_density_integral (n : ℕ) :
    (∫⁻ _x in pieces d f U hU hf ε hε n,
      ENNReal.ofReal (C1GraphDensityControl.density
        (linear d f U hU hf ε hε n)) ∂domainMeasure d) =
      ENNReal.ofReal (C1GraphDensityControl.density
        (linear d f U hU hf ε hε n)) *
        domainMeasure d (pieces d f U hU hf ε hε n) := by
  exact setLIntegral_const _ _

theorem density_piece_bounds (n : ℕ) (x : E d)
    (hx : x ∈ pieces d f U hU hf ε hε n) :
    ENNReal.ofReal (1 - ε) *
        ENNReal.ofReal (C1GraphDensityControl.density
          (linear d f U hU hf ε hε n)) ≤ densityAt d f x ∧
      densityAt d f x ≤ ENNReal.ofReal (1 + ε) *
        ENNReal.ofReal (C1GraphDensityControl.density
          (linear d f U hU hf ε hε n)) := by
  exact C1GraphDensityControl.ofReal_multiplicative_bounds
    (fderiv ℝ f x) (linear d f U hU hf ε hε n) ε hε.le
    (derivative_proximity d f U hU hf ε hε n x hx)

theorem selected_density_upper (n : ℕ) (x : E d)
    (hx : x ∈ pieces d f U hU hf ε hε n) :
    ENNReal.ofReal (C1GraphDensityControl.density
        (linear d f U hU hf ε hε n)) ≤
      ENNReal.ofReal (1 + ε) * densityAt d f x := by
  exact (C1GraphDensityControl.ofReal_multiplicative_bounds
    (linear d f U hU hf ε hε n) (fderiv ℝ f x) ε hε.le
    (by simpa [norm_sub_rev] using derivative_proximity d f U hU hf ε hε n x hx)).2

theorem dimension_two (f : E 2 → ℝ) (U : Set (E 2))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (ε : ℝ) (hε : 0 < ε) :
    ambientMeasure 2 (GraphMetricComparison.Graph 2 f U) =
      ∑' n, ambientMeasure 2
        (GraphMetricComparison.Graph 2 f (pieces 2 f U hU hf ε hε n)) :=
  graph_measure_sum 2 f U hU hf ε hε

theorem dimension_three (f : E 3 → ℝ) (U : Set (E 3))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (ε : ℝ) (hε : 0 < ε) :
    (∫⁻ x in U, densityAt 3 f x ∂domainMeasure 3) =
      ∑' n, ∫⁻ x in pieces 3 f U hU hf ε hε n,
        densityAt 3 f x ∂domainMeasure 3 :=
  density_integral_sum 3 f U hU hf ε hε

#print axioms densityAt_value
#print axioms densityAt_continuousOn
#print axioms graph_measure_sum
#print axioms density_integral_sum
#print axioms selected_density_integral
#print axioms density_piece_bounds
#print axioms selected_density_upper
#print axioms dimension_two
#print axioms dimension_three

end ConstructionTargets.C1GraphMeasureDecomposition
