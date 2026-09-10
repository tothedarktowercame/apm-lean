import ConstructionTargets.ENNRealCountableBounds
import ConstructionTargets.ENNRealMultiplicativeSqueeze

noncomputable section
namespace ConstructionTargets.C1GraphGlobalBounds

open Set MeasureTheory
open scoped ENNReal
open LinearGraphMeasure C1GraphPartition C1GraphMeasureDecomposition

variable (d : ℕ) (f : E d → ℝ) (U : Set (E d))
variable (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (ε : ℝ)
variable (hε : 0 < ε) (hε1 : ε < 1)

abbrev a : ℝ≥0∞ := ENNReal.ofReal (1 - ε)
abbrev b : ℝ≥0∞ := ENNReal.ofReal (1 + ε)
abbrev P (n : ℕ) : Set (E d) := pieces d f U hU hf ε hε n
abbrev D (n : ℕ) : ℝ≥0∞ := ENNReal.ofReal
  (C1GraphDensityControl.density (linear d f U hU hf ε hε n))
abbrev I (n : ℕ) : ℝ≥0∞ := ∫⁻ x in P d f U hU hf ε hε n,
  densityAt d f x ∂domainMeasure d
abbrev G (n : ℕ) : ℝ≥0∞ := ambientMeasure d
  (GraphMetricComparison.Graph d f (P d f U hU hf ε hε n))

theorem integral_upper (n : ℕ) :
    I d f U hU hf ε hε n ≤ b ε * D d f U hU hf ε hε n *
      domainMeasure d (P d f U hU hf ε hε n) := by
  exact (ENNRealCountableBounds.set_integral_bounds (domainMeasure d)
    (P d f U hU hf ε hε n) (pieces_measurable d f U hU hf ε hε n)
    (a ε) (b ε) (D d f U hU hf ε hε n) (densityAt d f)
    (fun x hx => (density_piece_bounds d f U hU hf ε hε n x hx).1)
    (fun x hx => (density_piece_bounds d f U hU hf ε hε n x hx).2)).2

theorem selected_integral_upper (n : ℕ) :
    D d f U hU hf ε hε n * domainMeasure d (P d f U hU hf ε hε n) ≤
      b ε * I d f U hU hf ε hε n := by
  rw [← selected_density_integral d f U hU hf ε hε n]
  calc
    _ ≤ ∫⁻ x in P d f U hU hf ε hε n,
        b ε * densityAt d f x ∂domainMeasure d :=
      setLIntegral_mono' (pieces_measurable d f U hU hf ε hε n)
        (fun x hx => selected_density_upper d f U hU hf ε hε n x hx)
    _ = _ := by
      rw [lintegral_const_mul']
      simp [b, ENNReal.ofReal_ne_top]

theorem ab_le_one (hε : 0 < ε) (hε1 : ε < 1) : a ε * b ε ≤ 1 := by
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 1 - ε)]
  apply ENNReal.ofReal_le_one.mpr
  nlinarith

theorem piece_global_bounds (hε1 : ε < 1) (n : ℕ) :
    (a ε) ^ (d + 1) * I d f U hU hf ε hε n ≤ G d f U hU hf ε hε n ∧
      G d f U hU hf ε hε n ≤
        (b ε) ^ (d + 1) * I d f U hU hf ε hε n := by
  obtain ⟨hgl, hgu⟩ := piece_bounds d f U hU hf ε hε hε1 n
  rw [← C1GraphDensityControl.density_eq_sqrt] at hgl hgu
  constructor
  · calc
      (a ε) ^ (d + 1) * I d f U hU hf ε hε n
          ≤ (a ε) ^ (d + 1) *
              (b ε * D d f U hU hf ε hε n *
                domainMeasure d (P d f U hU hf ε hε n)) := by
            gcongr
            exact integral_upper d f U hU hf ε hε n
      _ ≤ (a ε) ^ d * D d f U hU hf ε hε n *
              domainMeasure d (P d f U hU hf ε hε n) := by
            rw [pow_succ]
            calc
              ((a ε) ^ d * a ε) * (b ε * D d f U hU hf ε hε n *
                    domainMeasure d (P d f U hU hf ε hε n)) =
                  (a ε) ^ d * (a ε * b ε) * D d f U hU hf ε hε n *
                    domainMeasure d (P d f U hU hf ε hε n) := by ac_rfl
              _ ≤ (a ε) ^ d * 1 * D d f U hU hf ε hε n *
                    domainMeasure d (P d f U hU hf ε hε n) := by
                  gcongr
                  exact ab_le_one ε hε hε1
              _ = _ := by simp
      _ ≤ _ := hgl
  · calc
      G d f U hU hf ε hε n ≤
          (b ε) ^ d * D d f U hU hf ε hε n *
            domainMeasure d (P d f U hU hf ε hε n) := hgu
      _ = (b ε) ^ d * (D d f U hU hf ε hε n *
            domainMeasure d (P d f U hU hf ε hε n)) := by ac_rfl
      _ ≤ (b ε) ^ d * (b ε * I d f U hU hf ε hε n) :=
          mul_le_mul_right (selected_integral_upper d f U hU hf ε hε n) _
      _ = (b ε) ^ (d + 1) * I d f U hU hf ε hε n := by
          rw [pow_succ]
          ac_rfl

include hU hf hε in
theorem global_bounds (hε1 : ε < 1) :
    (a ε) ^ (d + 1) *
        (∫⁻ x in U, densityAt d f x ∂domainMeasure d) ≤
      ambientMeasure d (GraphMetricComparison.Graph d f U) ∧
    ambientMeasure d (GraphMetricComparison.Graph d f U) ≤
      (b ε) ^ (d + 1) *
        (∫⁻ x in U, densityAt d f x ∂domainMeasure d) := by
  exact ENNRealCountableBounds.global_bounds
    ((a ε) ^ (d + 1)) ((b ε) ^ (d + 1))
    (ambientMeasure d (GraphMetricComparison.Graph d f U))
    (∫⁻ x in U, densityAt d f x ∂domainMeasure d)
    (I d f U hU hf ε hε) (G d f U hU hf ε hε)
    (graph_measure_sum d f U hU hf ε hε)
    (density_integral_sum d f U hU hf ε hε)
    (fun n => (piece_global_bounds d f U hU hf ε hε hε1 n).1)
    (fun n => (piece_global_bounds d f U hU hf ε hε hε1 n).2)

theorem exact_area (d : ℕ) (f : E d → ℝ) (U : Set (E d))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ambientMeasure d (GraphMetricComparison.Graph d f U) =
      ∫⁻ x in U, densityAt d f x ∂domainMeasure d := by
  apply ENNRealMultiplicativeSqueeze.eq_of_bounds (d + 1)
  intro ε hε hε1
  exact global_bounds d f U hU hf ε hε hε1

theorem exact_area_value (d : ℕ) (f : E d → ℝ) (U : Set (E d))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ambientMeasure d (GraphMetricComparison.Graph d f U) =
      ∫⁻ x in U, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ f x‖ ^ 2))
        ∂domainMeasure d := by
  simpa only [densityAt_value] using exact_area d f U hU hf

theorem empty_domain (d : ℕ) (f : E d → ℝ) :
    ambientMeasure d (GraphMetricComparison.Graph d f ∅) =
      ∫⁻ x in (∅ : Set (E d)), densityAt d f x ∂domainMeasure d := by
  simpa using exact_area d f ∅ isOpen_empty (contDiffOn_empty : ContDiffOn ℝ 1 f ∅)

theorem zero_function (d : ℕ) (U : Set (E d)) (hU : IsOpen U) :
    ambientMeasure d (GraphMetricComparison.Graph d (fun _ => 0) U) =
      domainMeasure d U := by
  rw [exact_area_value d (fun _ => 0) U hU contDiffOn_const]
  simp

theorem dimension_two (f : E 2 → ℝ) (U : Set (E 2))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ambientMeasure 2 (GraphMetricComparison.Graph 2 f U) =
      ∫⁻ x in U, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ f x‖ ^ 2))
        ∂domainMeasure 2 := exact_area_value 2 f U hU hf

theorem dimension_three (f : E 3 → ℝ) (U : Set (E 3))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) :
    ambientMeasure 3 (GraphMetricComparison.Graph 3 f U) =
      ∫⁻ x in U, ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ f x‖ ^ 2))
        ∂domainMeasure 3 := exact_area_value 3 f U hU hf

#print axioms integral_upper
#print axioms selected_integral_upper
#print axioms ab_le_one
#print axioms piece_global_bounds
#print axioms global_bounds
#print axioms exact_area
#print axioms exact_area_value
#print axioms empty_domain
#print axioms zero_function
#print axioms dimension_two
#print axioms dimension_three

end ConstructionTargets.C1GraphGlobalBounds
