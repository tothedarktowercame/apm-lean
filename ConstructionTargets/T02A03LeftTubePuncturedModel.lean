import ConstructionTargets.T02A03GeometricTubeCover

noncomputable section

namespace ConstructionTargets.T02A03LeftTubePuncturedModel

open ConstructionTargets.T02A03GeometricTubeCover

theorem apm_t02a03_leftTubeRadialPoint_mem_leftTube
    (tp : unitInterval × apm_t02a03_LeftTubeMinusCore) :
    apm_t02a03_leftTubeRadialPoint tp ∈ apm_t02a03_leftTube := by
  let c := apm_t02a03_leftCoreCircle
    (apm_t02a03_leftTubeAngular ⟨tp.2.1, tp.2.2.1⟩)
  let x := (apm_t02a03_leftTubeTorusInverse
    (apm_t02a03_leftTubeTorusCoordinates tp.2)).1
  have hc : c ∈ Set.range apm_t02a03_leftCore := by
    rw [← apm_t02a03_range_leftCoreCircle]
    exact ⟨apm_t02a03_leftTubeAngular ⟨tp.2.1, tp.2.2.1⟩, rfl⟩
  have hx : x ∈ Metric.closedBall c (1 / 4 : ℝ) := by
    rw [Metric.mem_closedBall]
    have hd := apm_t02a03_dist_leftTubeTorusPoint_leftCoreCircle
      (apm_t02a03_leftTubeTorusCoordinates tp.2)
    change dist x c ≤ (1 / 4 : ℝ)
    have hd' : dist x c = (1 / 8 : ℝ) := by
      simpa [x, c, apm_t02a03_leftTubeTorusCoordinates] using hd
    rw [hd']
    norm_num
  have hp : tp.2.1 ∈ Metric.closedBall c (1 / 4 : ℝ) := by
    rw [Metric.mem_closedBall]
    change dist tp.2.1
      (apm_t02a03_leftCoreCircle
        (apm_t02a03_leftTubeAngular ⟨tp.2.1, tp.2.2.1⟩)) ≤ (1 / 4 : ℝ)
    rw [apm_t02a03_dist_leftTubePoint_angularCore
      (p := ⟨tp.2.1, tp.2.2.1⟩)]
    exact apm_t02a03_leftTubeNormalComplex_norm_le ⟨tp.2.1, tp.2.2.1⟩
  have ht0 : 0 ≤ (tp.1 : ℝ) := tp.1.2.1
  have ht1 : (tp.1 : ℝ) ≤ 1 := tp.1.2.2
  have hsegment :
      (1 - (tp.1 : ℝ)) • x + (tp.1 : ℝ) • tp.2.1 ∈
        segment ℝ x tp.2.1 :=
    ⟨1 - (tp.1 : ℝ), (tp.1 : ℝ), sub_nonneg.mpr ht1, ht0, by ring, rfl⟩
  have hcombo :
      (1 - (tp.1 : ℝ)) • x + (tp.1 : ℝ) • tp.2.1 ∈
        Metric.closedBall c (1 / 4 : ℝ) :=
    ((convex_closedBall c (1 / 4 : ℝ)).segment_subset hx hp) hsegment
  rw [apm_t02a03_leftTube,
    apm_t02a03_isCompact_range_leftCore.cthickening_eq_biUnion_closedBall
      (by norm_num)]
  simp only [Set.mem_iUnion]
  refine ⟨c, hc, ?_⟩
  simpa [apm_t02a03_leftTubeRadialPoint, x] using hcombo

theorem apm_t02a03_leftTubeRadialNormalRadius_pos
    (tp : unitInterval × apm_t02a03_LeftTubeMinusCore) :
    0 < (1 - (tp.1 : ℝ)) * (1 / 8 : ℝ) +
      (tp.1 : ℝ) *
        ‖apm_t02a03_leftTubeNormalComplex ⟨tp.2.1, tp.2.2.1⟩‖ := by
  have hz : apm_t02a03_leftTubeNormalComplex
      ⟨tp.2.1, tp.2.2.1⟩ ≠ 0 := by
    intro h
    exact (tp.2.property).2
      ((apm_t02a03_leftTubeNormalComplex_eq_zero_iff
        ⟨tp.2.1, tp.2.2.1⟩).mp h)
  have hn : 0 < ‖apm_t02a03_leftTubeNormalComplex
      ⟨tp.2.1, tp.2.2.1⟩‖ := norm_pos_iff.mpr hz
  have ht0 : 0 ≤ (tp.1 : ℝ) := tp.1.2.1
  have ht1 : (tp.1 : ℝ) ≤ 1 := tp.1.2.2
  by_cases ht : (tp.1 : ℝ) = 1
  · simp [ht, hn]
  · have hlt : (tp.1 : ℝ) < 1 := lt_of_le_of_ne ht1 ht
    have hfirst : 0 < (1 - (tp.1 : ℝ)) * (1 / 8 : ℝ) :=
      mul_pos (sub_pos.mpr hlt) (by norm_num)
    have hsecond : 0 ≤ (tp.1 : ℝ) *
        ‖apm_t02a03_leftTubeNormalComplex
          ⟨tp.2.1, tp.2.2.1⟩‖ :=
      mul_nonneg ht0 (norm_nonneg _)
    exact add_pos_of_pos_of_nonneg hfirst hsecond

end ConstructionTargets.T02A03LeftTubePuncturedModel
