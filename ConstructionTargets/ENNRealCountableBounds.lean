import ConstructionTargets.C1GraphMeasureDecomposition

noncomputable section
namespace ConstructionTargets.ENNRealCountableBounds

open MeasureTheory
open scoped ENNReal

theorem sum_bounds (a b : ℝ≥0∞) (I G : ℕ → ℝ≥0∞)
    (hl : ∀ n, a * I n ≤ G n) (hu : ∀ n, G n ≤ b * I n) :
    a * (∑' n, I n) ≤ ∑' n, G n ∧ (∑' n, G n) ≤ b * (∑' n, I n) := by
  constructor
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hl
  · rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hu

theorem global_bounds (a b A B : ℝ≥0∞) (I G : ℕ → ℝ≥0∞)
    (hA : A = ∑' n, G n) (hB : B = ∑' n, I n)
    (hl : ∀ n, a * I n ≤ G n) (hu : ∀ n, G n ≤ b * I n) :
    a * B ≤ A ∧ A ≤ b * B := by
  simpa [hA, hB] using sum_bounds a b I G hl hu

theorem set_integral_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Set X) (hs : MeasurableSet s)
    (a b c : ℝ≥0∞) (J : X → ℝ≥0∞)
    (hl : ∀ x ∈ s, a * c ≤ J x) (hu : ∀ x ∈ s, J x ≤ b * c) :
    a * c * μ s ≤ (∫⁻ x in s, J x ∂μ) ∧
      (∫⁻ x in s, J x ∂μ) ≤ b * c * μ s := by
  constructor
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hs hl
  · rw [← setLIntegral_const]
    exact setLIntegral_mono' hs hu

theorem zero_example (G : ℕ → ℝ≥0∞) (h : ∀ n, G n = 0) :
    (∑' n, G n) = 0 := by
  simp [h]

theorem infinite_example :
    (1 : ℝ≥0∞) * (∞ : ℝ≥0∞) ≤ ∞ ∧ (∞ : ℝ≥0∞) ≤ 1 * ∞ := by
  simp

#print axioms sum_bounds
#print axioms global_bounds
#print axioms set_integral_bounds
#print axioms zero_example
#print axioms infinite_example

end ConstructionTargets.ENNRealCountableBounds
