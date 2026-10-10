import ConstructionTargets.PolygonAnnularOverlapHomeomorph
import Mathlib.Analysis.Normed.Module.Normalize

open Set Topology
noncomputable section

namespace ConstructionTargets.PolygonAnnulusRadialMaps

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonRadialOpenCover
open ConstructionTargets.PolygonAnnularOverlapHomeomorph

/-- Include the complex unit circle at radius one half in the polygon annulus. -/
def halfCircleMap : C(Circle, Annulus) where
  toFun z := ⟨⟨(1 / 2 : ℂ) * (z.1 : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Circle.norm_coe]
    norm_num⟩, by
      constructor
      · change ‖(1 / 2 : ℂ) * (z.1 : ℂ)‖ < 3 / 4
        rw [norm_mul, Circle.norm_coe]
        norm_num
      · change 1 / 4 < ‖(1 / 2 : ℂ) * (z.1 : ℂ)‖
        rw [norm_mul, Circle.norm_coe]
        norm_num⟩
  continuous_toFun := by fun_prop

/-- Radially normalize an annular point onto the complex unit circle. -/
def radialNormalizeMap : C(Annulus, Circle) where
  toFun x := ⟨((‖(x.1.1 : ℂ)‖⁻¹ : ℝ) : ℂ) * x.1.1, by
    show ((‖(x.1.1 : ℂ)‖⁻¹ : ℝ) : ℂ) * x.1.1 ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    apply inv_mul_cancel₀
    intro hx
    have hr : 1 / 4 < ‖(x.1.1 : ℂ)‖ := x.2.2
    rw [hx] at hr
    norm_num at hr⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    rw [continuous_iff_continuousAt]
    intro x
    have hc : Continuous (fun y : Annulus => ‖(y.1.1 : ℂ)‖) :=
      continuous_norm.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hx0 : (x.1.1 : ℂ) ≠ 0 := by
      intro hx
      have hr : 1 / 4 < ‖(x.1.1 : ℂ)‖ := x.2.2
      rw [hx, norm_zero] at hr
      norm_num at hr
    exact ((Complex.continuous_ofReal.continuousAt.comp
      (hc.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx0))).mul
      (continuous_subtype_val.comp continuous_subtype_val).continuousAt)

theorem radialNormalize_halfCircle (z : Circle) :
    radialNormalizeMap (halfCircleMap z) = z := by
  apply Subtype.ext
  change ((‖(1 / 2 : ℂ) * (z.1 : ℂ)‖⁻¹ : ℝ) : ℂ) *
      ((1 / 2 : ℂ) * z.1) = z.1
  rw [norm_mul, Circle.norm_coe]
  norm_num
  ring

end ConstructionTargets.PolygonAnnulusRadialMaps
