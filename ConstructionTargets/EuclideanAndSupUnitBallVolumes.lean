import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory Metric
open scoped ENNReal

namespace ConstructionTargets.EuclideanAndSupUnitBallVolumes

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem euclidean_two :
    volume (ball (0 : E2) 1) = ENNReal.ofReal Real.pi := by
  rw [EuclideanSpace.volume_ball_fin_two]
  norm_num

theorem euclidean_three :
    volume (ball (0 : E3) 1) = ENNReal.ofReal (Real.pi * 4 / 3) := by
  rw [EuclideanSpace.volume_ball_fin_three]
  norm_num

theorem sup_two :
    volume (ball (0 : Fin 2 → ℝ) 1) = 4 := by
  rw [volume_pi_ball (0 : Fin 2 → ℝ) (by norm_num)]
  norm_num

theorem sup_three :
    volume (ball (0 : Fin 3 → ℝ) 1) = 8 := by
  rw [volume_pi_ball (0 : Fin 3 → ℝ) (by norm_num)]
  norm_num

#print axioms euclidean_two
#print axioms euclidean_three
#print axioms sup_two
#print axioms sup_three

end ConstructionTargets.EuclideanAndSupUnitBallVolumes
