import ConstructionTargets.EuclideanTriangleMeasureFubini

/-! # Final finite-coordinate Fubini calculation for the standard triangle

This file identifies `volume` on `Fin 2 → ℝ` with two-dimensional product
Lebesgue measure and applies Fubini to the literal triangular indicator.
-/

open MeasureTheory Set
noncomputable section

namespace ConstructionTargets.FinTwoTriangleFubiniFinal

open ConstructionTargets.ExteriorDerivativeSimplexCalculus
open ConstructionTargets.FrozenSimplexIntegralAdapter
open ConstructionTargets.EuclideanTriangleMeasureFubini

def productTriangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem measurableSet_productTriangle : MeasurableSet productTriangle := by
  have hx : Continuous (fun p : ℝ × ℝ => p.1) := continuous_fst
  have hy : Continuous (fun p : ℝ × ℝ => p.2) := continuous_snd
  unfold productTriangle
  change MeasurableSet
    ({p : ℝ × ℝ | 0 ≤ p.1} ∩
      ({p | 0 ≤ p.2} ∩ {p | p.1 + p.2 ≤ 1}))
  exact (measurableSet_le measurable_const hx.measurable).inter
    ((measurableSet_le measurable_const hy.measurable).inter
      (measurableSet_le (hx.add hy).measurable measurable_const))

theorem finTwoArrow_mem_productTriangle_iff (q : Fin 2 → ℝ) :
    (MeasurableEquiv.finTwoArrow q : ℝ × ℝ) ∈ productTriangle ↔
      q ∈ coordinateTriangle := by
  simp [productTriangle, coordinateTriangle, MeasurableEquiv.finTwoArrow]

theorem coordinateIntegral_eq_productTriangleIntegral :
    (∫ q in coordinateTriangle, (2 : ℝ)) =
      ∫ p in productTriangle, (2 : ℝ) := by
  rw [← integral_indicator measurableSet_coordinateTriangle,
    ← integral_indicator measurableSet_productTriangle]
  rw [← (volume_preserving_finTwoArrow ℝ).integral_comp
    (MeasurableEquiv.finTwoArrow : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards [] with q
  by_cases hq : q ∈ coordinateTriangle
  · rw [indicator_of_mem hq,
      indicator_of_mem ((finTwoArrow_mem_productTriangle_iff q).mpr hq)]
  · have hnot : MeasurableEquiv.finTwoArrow q ∉ productTriangle :=
      fun h => hq ((finTwoArrow_mem_productTriangle_iff q).mp h)
    change (q 0, q 1) ∉ productTriangle at hnot
    simp [Set.indicator, hq, hnot]

theorem productTriangle_subset_box :
    productTriangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := by
  intro p hp
  rcases hp with ⟨hx, hy, hxy⟩
  exact ⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩

theorem integrable_productTriangle_indicator :
    Integrable (productTriangle.indicator fun _ : ℝ × ℝ => (2 : ℝ)) := by
  rw [integrable_indicator_iff measurableSet_productTriangle]
  exact integrableOn_const (C := (2 : ℝ))
    (ne_top_of_le_ne_top ((isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne)
      (measure_mono productTriangle_subset_box))

theorem productTriangleIntegral_eq_iterated :
    (∫ p in productTriangle, (2 : ℝ)) =
      ∫ x : ℝ, ∫ y : ℝ,
        productTriangle.indicator (fun _ : ℝ × ℝ => (2 : ℝ)) (x, y) := by
  rw [← integral_indicator measurableSet_productTriangle]
  exact integral_prod _ integrable_productTriangle_indicator

theorem productTriangleIntegral_eq_orientedTriangleIntegral :
    (∫ p in productTriangle, (2 : ℝ)) =
      orientedTriangleIntegral (fun _ _ => 2) := by
  rw [productTriangleIntegral_eq_iterated]
  simp only [productTriangle, Set.indicator, mem_setOf_eq]
  have hfiber (x : ℝ) :
      (∫ y : ℝ, if 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 then (2 : ℝ) else 0) =
        (Icc (0 : ℝ) 1).indicator
          (fun x => ∫ y in Icc (0 : ℝ) (1 - x), (2 : ℝ)) x := by
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [indicator_of_mem hx, ← integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ Icc (0 : ℝ) (1 - x)
      · rw [indicator_of_mem hy]
        rw [if_pos ⟨hx.1, hy.1, by linarith [hy.2]⟩]
      · simp only [indicator_of_notMem hy]
        simp only [mem_Icc, not_and_or] at hy
        split_ifs with h
        · rcases h with ⟨_, hy0, hxy⟩
          rcases hy with hy | hy
          · exact False.elim (hy hy0)
          · exact False.elim (hy (by linarith))
        · rfl
    · rw [indicator_of_notMem hx]
      apply integral_eq_zero_of_ae
      filter_upwards [] with y
      split_ifs with h
      · rcases h with ⟨hx0, _, hxy⟩
        exfalso
        apply hx
        exact ⟨hx0, by linarith⟩
      · rfl
  calc
    (∫ x : ℝ, ∫ y : ℝ,
        if 0 ≤ x ∧ 0 ≤ y ∧ x + y ≤ 1 then (2 : ℝ) else 0) =
        ∫ x in Icc (0 : ℝ) 1, ∫ y in Icc (0 : ℝ) (1 - x), (2 : ℝ) := by
          rw [← integral_indicator measurableSet_Icc]
          exact integral_congr_ae (Filter.Eventually.of_forall hfiber)
    _ = 1 := by
      have hinner (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
          (∫ y in Icc (0 : ℝ) (1 - x), (2 : ℝ)) = 2 * (1 - x) := by
        rw [setIntegral_const]
        simp [measureReal_def, Real.volume_Icc, hx.2]
        ring
      rw [setIntegral_congr_fun measurableSet_Icc (fun x hx => hinner x hx)]
      rw [show (∫ x in Icc (0 : ℝ) 1, 2 * (1 - x)) =
          ∫ x in (0 : ℝ)..1, 2 * (1 - x) by
        rw [intervalIntegral.integral_of_le (by norm_num)]
        exact setIntegral_congr_set Ioc_ae_eq_Icc.symm]
      rw [intervalIntegral.integral_const_mul]
      have hsub : (∫ x : ℝ in (0 : ℝ)..1, 1 - x) =
          (∫ _x : ℝ in (0 : ℝ)..1, (1 : ℝ)) - ∫ x : ℝ in (0 : ℝ)..1, x := by
        simpa only [Pi.one_apply, Pi.sub_apply, id_eq] using
          (intervalIntegral.integral_sub
            (continuous_const.intervalIntegrable 0 1)
            (continuous_id.intervalIntegrable 0 1))
      rw [hsub]
      rw [show (∫ x : ℝ in (0 : ℝ)..1, x) = 1 / 2 by
        simpa using (integral_pow (a := (0 : ℝ)) (b := 1) 1)]
      norm_num
    _ = orientedTriangleIntegral (fun _ _ => 2) :=
      integral_const_two_triangle.symm

/-- The formerly isolated finite-product normalization. -/
theorem finTwoTriangleFubini : FinTwoTriangleFubini := by
  rw [FinTwoTriangleFubini]
  rw [coordinateIntegral_eq_productTriangleIntegral]
  exact productTriangleIntegral_eq_orientedTriangleIntegral

theorem frozenTriangleMeasureAdapter : FrozenTriangleMeasureAdapter :=
  frozenTriangleMeasureAdapter_of_finTwoFubini finTwoTriangleFubini

theorem frozenTriangleIntegral_value :
    frozenTriangleSetIntegral (fun _ => 2) = 1 :=
  frozen_triangle_integral_of_adapter frozenTriangleMeasureAdapter

#print axioms finTwoTriangleFubini
#print axioms frozenTriangleMeasureAdapter
#print axioms frozenTriangleIntegral_value

end ConstructionTargets.FinTwoTriangleFubiniFinal
