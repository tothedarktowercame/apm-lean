import ConstructionTargets.PolygonRadialOpenCover
import Mathlib.Analysis.Normed.Module.Normalize

open Set Topology
open unitInterval
noncomputable section

namespace ConstructionTargets.PolygonOuterRadialDeformation

open ConstructionTargets.Surfaces
open ConstructionTargets.PolygonRadialOpenCover

abbrev Outer := {x : Disk // x ∈ outerSource}

def scale (tx : I × Outer) : ℝ :=
  (1 - (tx.1 : ℝ)) + (tx.1 : ℝ) / radius tx.2.1

theorem radius_pos (x : Outer) : 0 < radius x.1 := by
  have hx : 1 / 4 < radius x.1 := x.2
  linarith

theorem scale_pos (tx : I × Outer) : 0 < scale tx := by
  have ht0 : 0 ≤ (tx.1 : ℝ) := tx.1.2.1
  have ht1 : (tx.1 : ℝ) ≤ 1 := tx.1.2.2
  have hr := radius_pos tx.2
  have hdiv : 0 ≤ (tx.1 : ℝ) / radius tx.2.1 := div_nonneg ht0 hr.le
  dsimp [scale]
  by_cases ht : (tx.1 : ℝ) = 1
  · rw [ht]
    simpa using (one_div_pos.mpr hr)
  · have : 0 < 1 - (tx.1 : ℝ) := sub_pos.mpr (lt_of_le_of_ne ht1 ht)
    linarith

theorem scale_mul_radius (tx : I × Outer) :
    scale tx * radius tx.2.1 =
      (1 - (tx.1 : ℝ)) * radius tx.2.1 + (tx.1 : ℝ) := by
  have hr : radius tx.2.1 ≠ 0 := (radius_pos tx.2).ne'
  dsimp [scale]
  field_simp

def radialHomotopy (tx : I × Outer) : Outer := by
  let a := scale tx
  let z : ℂ := tx.2.1.1
  have hr0 : 0 < radius tx.2.1 := radius_pos tx.2
  have hr1 : radius tx.2.1 ≤ 1 := by
    have h := tx.2.1.2
    change dist (tx.2.1.1 : ℂ) 0 ≤ 1 at h
    simpa [dist_zero_right, radius] using h
  have ha : 0 < a := scale_pos tx
  have hnorm : ‖(a : ℂ) * z‖ = a * radius tx.2.1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
    rfl
  refine ⟨⟨(a : ℂ) * z, ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, hnorm, scale_mul_radius]
    have ht0 : 0 ≤ (tx.1 : ℝ) := tx.1.2.1
    have ht1 : (tx.1 : ℝ) ≤ 1 := tx.1.2.2
    nlinarith
  · change 1 / 4 < ‖(a : ℂ) * z‖
    rw [hnorm, scale_mul_radius]
    have ht0 : 0 ≤ (tx.1 : ℝ) := tx.1.2.1
    have ht1 : (tx.1 : ℝ) ≤ 1 := tx.1.2.2
    have hx : 1 / 4 < radius tx.2.1 := tx.2.2
    nlinarith

theorem continuous_radialHomotopy : Continuous radialHomotopy := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have ht : Continuous (fun tx : I × Outer => (tx.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hz : Continuous (fun tx : I × Outer => tx.2.1.1) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have hr : Continuous (fun tx : I × Outer => radius tx.2.1) :=
    continuous_radius.comp (continuous_subtype_val.comp continuous_snd)
  have hr0 : ∀ tx : I × Outer, radius tx.2.1 ≠ 0 :=
    fun tx => (radius_pos tx.2).ne'
  exact (Complex.continuous_ofReal.comp
    ((continuous_const.sub ht).add (ht.div hr hr0))).mul hz

theorem radialHomotopy_zero (x : Outer) : radialHomotopy (0, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  simp [radialHomotopy, scale]

theorem radialHomotopy_one_radius (x : Outer) :
    radius (radialHomotopy (1, x)).1 = 1 := by
  change ‖((radialHomotopy (1, x)).1.1 : ℂ)‖ = 1
  simp only [radialHomotopy]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hr := radius_pos x
  dsimp [scale]
  simp only [sub_self, zero_add]
  change |(1 / radius x.1 : ℝ)| * radius x.1 = 1
  rw [abs_of_pos (one_div_pos.mpr hr), one_div_mul_cancel hr.ne']

theorem radialHomotopy_fixed_of_radius_one (t : I) (x : Outer)
    (hx : radius x.1 = 1) : radialHomotopy (t, x) = x := by
  apply Subtype.ext
  apply Subtype.ext
  simp [radialHomotopy, scale, hx]

end ConstructionTargets.PolygonOuterRadialDeformation
