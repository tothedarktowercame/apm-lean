import ConstructionTargets.PolygonAnnulusRadialMaps

open Set Topology
open unitInterval
noncomputable section

namespace ConstructionTargets.PolygonAnnulusRadialHomotopy

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonAnnularOverlapHomeomorph
open ConstructionTargets.PolygonAnnulusRadialMaps

def annulusRadialHomotopy : ContinuousMap.Homotopy
    (halfCircleMap.comp radialNormalizeMap) (ContinuousMap.id Annulus) where
  toFun tx := by
    let t : ℝ := tx.1
    let x : ℂ := tx.2.1.1
    let a : ℝ := (1 - t) * (1 / (2 * ‖x‖)) + t
    refine ⟨⟨(a : ℂ) * x, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have ht0 : 0 ≤ t := tx.1.2.1
      have ht1 : t ≤ 1 := tx.1.2.2
      have hx0 : 0 < ‖x‖ := lt_trans (by norm_num) tx.2.2.2
      have hx1 : ‖x‖ < 3 / 4 := tx.2.2.1
      have ha0 : 0 ≤ a := by
        dsimp [a]
        have hden : 0 < 1 / (2 * ‖x‖) := one_div_pos.mpr (mul_pos (by norm_num) hx0)
        have hfirst : 0 ≤ (1 - t) * (1 / (2 * ‖x‖)) :=
          mul_nonneg (sub_nonneg.mpr ht1) hden.le
        linarith
      rw [abs_of_nonneg ha0]
      have hxne : ‖x‖ ≠ 0 := hx0.ne'
      have ha_mul : a * ‖x‖ = (1 - t) / 2 + t * ‖x‖ := by
        dsimp [a]
        field_simp
      rw [ha_mul]
      nlinarith
    · constructor
      · change ‖(a : ℂ) * x‖ < 3 / 4
        rw [norm_mul]
        simp only [Complex.norm_real, Real.norm_eq_abs]
        have ht0 : 0 ≤ t := tx.1.2.1
        have ht1 : t ≤ 1 := tx.1.2.2
        have hx0 : 0 < ‖x‖ := lt_trans (by norm_num) tx.2.2.2
        have hx1 : ‖x‖ < 3 / 4 := tx.2.2.1
        have ha0 : 0 ≤ a := by
          dsimp [a]
          have hden : 0 < 1 / (2 * ‖x‖) := one_div_pos.mpr (mul_pos (by norm_num) hx0)
          have hfirst : 0 ≤ (1 - t) * (1 / (2 * ‖x‖)) :=
            mul_nonneg (sub_nonneg.mpr ht1) hden.le
          linarith
        rw [abs_of_nonneg ha0]
        have ha_mul : a * ‖x‖ = (1 - t) / 2 + t * ‖x‖ := by
          dsimp [a]
          field_simp
        rw [ha_mul]
        by_cases ht : t = 0
        · norm_num [ht]
        · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
          nlinarith
      · change 1 / 4 < ‖(a : ℂ) * x‖
        rw [norm_mul]
        simp only [Complex.norm_real, Real.norm_eq_abs]
        have ht0 : 0 ≤ t := tx.1.2.1
        have ht1 : t ≤ 1 := tx.1.2.2
        have hx0 : 0 < ‖x‖ := lt_trans (by norm_num) tx.2.2.2
        have hxq : 1 / 4 < ‖x‖ := tx.2.2.2
        have ha0 : 0 ≤ a := by
          dsimp [a]
          have hden : 0 < 1 / (2 * ‖x‖) := one_div_pos.mpr (mul_pos (by norm_num) hx0)
          have hfirst : 0 ≤ (1 - t) * (1 / (2 * ‖x‖)) :=
            mul_nonneg (sub_nonneg.mpr ht1) hden.le
          linarith
        rw [abs_of_nonneg ha0]
        have ha_mul : a * ‖x‖ = (1 - t) / 2 + t * ‖x‖ := by
          dsimp [a]
          field_simp
        rw [ha_mul]
        by_cases ht : t = 0
        · norm_num [ht]
        · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
          nlinarith
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hnorm : Continuous (fun tx : I × Annulus => ‖(tx.2.1.1 : ℂ)‖) :=
      continuous_norm.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
    have hne : ∀ tx : I × Annulus, 2 * ‖(tx.2.1.1 : ℂ)‖ ≠ 0 := by
      intro tx
      exact mul_ne_zero (by norm_num) (ne_of_gt (lt_trans (by norm_num) tx.2.2.2))
    have ht : Continuous (fun tx : I × Annulus => (tx.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun tx : I × Annulus => (tx.2.1.1 : ℂ)) :=
      continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
    exact (Complex.continuous_ofReal.comp
      (((continuous_const.sub ht).mul
        (continuous_const.div (continuous_const.mul hnorm) hne)).add ht)).mul hx
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp [halfCircleMap, radialNormalizeMap]
    norm_num
    ring
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    simp

def annulusHomotopyEquivCircle : ContinuousMap.HomotopyEquiv Circle Annulus where
  toFun := halfCircleMap
  invFun := radialNormalizeMap
  left_inv := by
    rw [show radialNormalizeMap.comp halfCircleMap = ContinuousMap.id Circle by
      apply ContinuousMap.ext
      intro z
      exact radialNormalize_halfCircle z]
  right_inv := ⟨annulusRadialHomotopy⟩

end ConstructionTargets.PolygonAnnulusRadialHomotopy
