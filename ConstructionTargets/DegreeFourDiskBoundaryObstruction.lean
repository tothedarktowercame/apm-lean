import ConstructionTargets.PeriodicCircleHomotopyWinding

/-! # The disk-extension half of the degree-four boundary obstruction -/

open Set
open scoped unitInterval
noncomputable section

namespace ConstructionTargets.DegreeFourDiskBoundaryObstruction

abbrev ComplexUnitDisk := Metric.closedBall (0 : ℂ) 1

/-- The fourth-power self-map of the circle. -/
def degreeFour : C(Circle, Circle) :=
  ⟨fun z => ⟨(z : ℂ) ^ 4, by
    simpa [Submonoid.unitSphere, norm_pow] using congrArg (· ^ 4) z.property⟩,
   by fun_prop⟩

/-- Radial contraction of the circle through the closed complex unit disk. -/
def radialDiskPoint (p : I × Circle) : ComplexUnitDisk :=
  ⟨(((1 : ℝ) - (p.1 : ℝ)) : ℂ) * (p.2 : ℂ), by
    rw [Metric.mem_closedBall, dist_zero_right, norm_mul]
    have hs : ‖(((1 : ℝ) - (p.1 : ℝ)) : ℂ)‖ = 1 - (p.1 : ℝ) := by
      change ‖(((1 : ℝ) : ℂ) - (((p.1 : ℝ) : ℂ)))‖ = _
      rw [← Complex.ofReal_sub]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr p.1.2.2)]
    have hz : ‖(p.2 : ℂ)‖ = 1 := by
      simpa [Submonoid.unitSphere] using p.2.property
    rw [hs, hz, mul_one]
    exact sub_le_self 1 p.1.2.1⟩

theorem radialDiskPoint_continuous : Continuous radialDiskPoint := by
  apply Continuous.subtype_mk
  change Continuous (fun p : I × Circle =>
    (((1 : ℝ) - (p.1 : ℝ)) : ℂ) * (p.2 : ℂ))
  fun_prop

def circleToDisk : C(Circle, ComplexUnitDisk) :=
  ⟨fun z => ⟨z.1, by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact le_of_eq (by simpa [Submonoid.unitSphere] using z.2)⟩,
   by fun_prop⟩

def diskZero : ComplexUnitDisk := ⟨0, by simp⟩

/-- Normalize a zero-free complex-valued disk map to a circle-valued map. -/
def normalizedDiskMap (F : ComplexUnitDisk → ℂ) (hF : Continuous F)
    (hF0 : ∀ z, F z ≠ 0) :
    C(ComplexUnitDisk, Circle) :=
  ⟨fun z => ⟨F z / ‖F z‖, by
      simpa [Submonoid.unitSphere, norm_div, hF0 z]⟩,
   by
    apply Continuous.subtype_mk
    exact hF.div (Complex.continuous_ofReal.comp hF.norm)
      (fun z => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hF0 z)))⟩

/-- A zero-free extension over the disk makes its normalized boundary loop
null-homotopic, by the literal radial contraction. -/
theorem normalized_boundary_homotopic_const
    (F : ComplexUnitDisk → ℂ) (hF : Continuous F) (hF0 : ∀ z, F z ≠ 0) :
    ContinuousMap.Homotopic
      ((normalizedDiskMap F hF hF0).comp circleToDisk)
      (ContinuousMap.const Circle (normalizedDiskMap F hF hF0 diskZero)) := by
  let N : C(ComplexUnitDisk, Circle) :=
    normalizedDiskMap F hF hF0
  let H : C(I × Circle, Circle) := N.comp
    ⟨radialDiskPoint, radialDiskPoint_continuous⟩
  exact ⟨{
    toContinuousMap := H
    map_zero_left := by
      intro z
      change N (radialDiskPoint (0, z)) = N (circleToDisk z)
      congr 1
      apply Subtype.ext
      simp [radialDiskPoint, circleToDisk]
    map_one_left := by
      intro z
      change N (radialDiskPoint (1, z)) = N diskZero
      congr 1
      apply Subtype.ext
      simp [radialDiskPoint, diskZero] }⟩

/-- Therefore any zero-free disk extension whose normalized boundary is the
fourth-power loop would supply a null-homotopy of that loop. -/
theorem degreeFour_homotopic_const_of_zeroFreeDiskExtension
    (F : ComplexUnitDisk → ℂ) (hF : Continuous F) (hF0 : ∀ z, F z ≠ 0)
    (hboundary : ∀ z : Circle,
      normalizedDiskMap F hF hF0 (circleToDisk z) = degreeFour z) :
    ContinuousMap.Homotopic degreeFour
      (ContinuousMap.const Circle (normalizedDiskMap F hF hF0 diskZero)) := by
  rcases normalized_boundary_homotopic_const F hF hF0 with ⟨H⟩
  exact ⟨{
    toContinuousMap := H.toContinuousMap
    map_zero_left := fun z => (H.map_zero_left z).trans (hboundary z)
    map_one_left := H.map_one_left }⟩

#print axioms radialDiskPoint_continuous
#print axioms normalized_boundary_homotopic_const
#print axioms degreeFour_homotopic_const_of_zeroFreeDiskExtension

end ConstructionTargets.DegreeFourDiskBoundaryObstruction
