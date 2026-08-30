import ConstructionTargets.DegreeFourCircleWinding

/-! # Radius-disk coordinates for the degree-four obstruction -/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.DegreeFourRadiusDiskAdapter

open ConstructionTargets.DegreeFourDiskBoundaryObstruction
open ConstructionTargets.DegreeFourCircleWinding

def rescaleDiskPoint (r : ℝ) (hr : 0 < r) (z : ComplexUnitDisk) : ℂ :=
  (r : ℂ) * z.1

theorem rescaleDiskPoint_mem (r : ℝ) (hr : 0 < r) (z : ComplexUnitDisk) :
    rescaleDiskPoint r hr z ∈ Metric.closedBall (0 : ℂ) r := by
  rw [Metric.mem_closedBall, dist_zero_right]
  simp only [rescaleDiskPoint, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  have hz : ‖(z.1 : ℂ)‖ ≤ 1 := by
    have hz0 := z.property
    rw [Metric.mem_closedBall, dist_zero_right] at hz0
    exact hz0
  exact mul_le_of_le_one_right (le_of_lt hr) hz

def radiusCirclePoint (r : ℝ) (hr : 0 < r) (z : Circle) :
    Metric.sphere (0 : ℂ) r :=
  ⟨(r : ℂ) * z.1, by
    rw [Metric.mem_sphere, dist_zero_right, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr]
    simpa [Submonoid.unitSphere] using congrArg (r * ·) z.2⟩

theorem radiusCirclePoint_continuous (r : ℝ) (hr : 0 < r) :
    Continuous (radiusCirclePoint r hr) := by
  apply Continuous.subtype_mk
  fun_prop

def rescaledDiskMap (F : ℂ → ℂ) (r : ℝ) (hr : 0 < r) : ComplexUnitDisk → ℂ :=
  fun z ↦ F (rescaleDiskPoint r hr z)

theorem rescaledDiskMap_continuous (F : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hF : Continuous F) : Continuous (rescaledDiskMap F r hr) := by
  exact hF.comp (by unfold rescaleDiskPoint; fun_prop)

private def normalizedBoundaryHomotopy
    (r : ℝ) (H : I × Metric.sphere (0 : ℂ) r → ℂ)
    (hH_cont : Continuous H) (hH_ne : ∀ p, H p ≠ 0)
    (hr : 0 < r) : C(I × Circle, Circle) :=
  ⟨fun p ↦ ⟨H (p.1, radiusCirclePoint r hr p.2) /
      ‖H (p.1, radiusCirclePoint r hr p.2)‖, by
        simp [Submonoid.unitSphere, norm_div, hH_ne]⟩, by
    apply Continuous.subtype_mk
    exact (hH_cont.comp (continuous_fst.prodMk
      ((radiusCirclePoint_continuous r hr).comp continuous_snd))).div
        (Complex.continuous_ofReal.comp
          (hH_cont.comp (continuous_fst.prodMk
            ((radiusCirclePoint_continuous r hr).comp continuous_snd))).norm)
        (fun p ↦ Complex.ofReal_ne_zero.mpr
          (norm_ne_zero_iff.mpr (hH_ne (p.1, radiusCirclePoint r hr p.2))))⟩

private theorem normalized_fourth_power (r : ℝ) (hr : 0 < r) (z : Circle) :
    (((r : ℂ) * z.1) ^ 4) / ‖((r : ℂ) * z.1) ^ 4‖ = z.1 ^ 4 := by
  rw [mul_pow, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr]
  have hz : ‖(z : ℂ)‖ = 1 := by simpa [Submonoid.unitSphere] using z.2
  rw [norm_pow, hz]
  norm_num
  field_simp [ne_of_gt hr]

private theorem boundaryHomotopy_from_cylinder
    (F : ℂ → ℂ) (r : ℝ) (hr : 0 < r)
    (hF : Continuous F)
    (H : I × Metric.sphere (0 : ℂ) r → ℂ)
    (hH_cont : Continuous H) (hH_ne : ∀ p, H p ≠ 0)
    (hH_zero : ∀ z : Metric.sphere (0 : ℂ) r, H (0, z) = z.1 ^ 4)
    (hH_one : ∀ z : Metric.sphere (0 : ℂ) r, H (1, z) = F z.1)
    (hF0 : ∀ z : ComplexUnitDisk, rescaledDiskMap F r hr z ≠ 0) :
    ContinuousMap.Homotopic degreeFour
      ((normalizedDiskMap (rescaledDiskMap F r hr)
        (rescaledDiskMap_continuous F r hr hF) hF0).comp circleToDisk) := by
  let Q := normalizedBoundaryHomotopy r H hH_cont hH_ne hr
  refine ⟨{
    toContinuousMap := Q
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    apply Subtype.ext
    change ((Q (0, z) : Circle) : ℂ) = ((degreeFour z : Circle) : ℂ)
    simp only [Q, normalizedBoundaryHomotopy, degreeFour]
    change H (0, radiusCirclePoint r hr z) /
        ‖H (0, radiusCirclePoint r hr z)‖ = z.1 ^ 4
    rw [hH_zero]
    exact normalized_fourth_power r hr z
  · intro z
    apply Subtype.ext
    change ((Q (1, z) : Circle) : ℂ) =
      ((((normalizedDiskMap (rescaledDiskMap F r hr)
        (rescaledDiskMap_continuous F r hr hF) hF0).comp circleToDisk) z : Circle) : ℂ)
    simp only [Q, normalizedBoundaryHomotopy, normalizedDiskMap,
      ContinuousMap.comp_apply, circleToDisk]
    change H (1, radiusCirclePoint r hr z) /
        ‖H (1, radiusCirclePoint r hr z)‖ =
      F (rescaleDiskPoint r hr (circleToDisk z)) /
        ‖F (rescaleDiskPoint r hr (circleToDisk z))‖
    rw [hH_one]
    rfl

/-- Frozen-coordinate adapter: a zero-free cylinder from `z ^ 4` to the
boundary restriction of a continuous map forces that map to vanish in the
radius-`r` closed disk. -/
theorem exists_zero_in_closedBall_of_degreeFour_boundaryHomotopy
    (F : ℂ → ℂ) (r : ℝ) (hr : 0 < r) (hF : Continuous F)
    (H : I × Metric.sphere (0 : ℂ) r → ℂ)
    (hH_cont : Continuous H) (hH_ne : ∀ p, H p ≠ 0)
    (hH_zero : ∀ z : Metric.sphere (0 : ℂ) r, H (0, z) = z.1 ^ 4)
    (hH_one : ∀ z : Metric.sphere (0 : ℂ) r, H (1, z) = F z.1) :
    ∃ z ∈ Metric.closedBall (0 : ℂ) r, F z = 0 := by
  let G := rescaledDiskMap F r hr
  have hG : Continuous G := rescaledDiskMap_continuous F r hr hF
  by_contra hz
  push_neg at hz
  have hG0 : ∀ z : ComplexUnitDisk, G z ≠ 0 := by
    intro z
    exact hz (rescaleDiskPoint r hr z) (rescaleDiskPoint_mem r hr z)
  have hhom := boundaryHomotopy_from_cylinder F r hr hF H hH_cont hH_ne
    hH_zero hH_one hG0
  obtain ⟨z, hz0⟩ := exists_zero_of_degreeFour_homotopic_normalizedBoundary
    G hG (fun _ ↦ hhom)
  exact hG0 z hz0

#print axioms rescaleDiskPoint_mem
#print axioms normalized_fourth_power
#print axioms exists_zero_in_closedBall_of_degreeFour_boundaryHomotopy

end ConstructionTargets.DegreeFourRadiusDiskAdapter
