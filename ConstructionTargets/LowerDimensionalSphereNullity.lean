import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

open MeasureTheory MeasureTheory.Measure Metric
open scoped MeasureTheory ENNReal

namespace ConstructionTargets.LowerDimensionalSphereNullity

abbrev E2 := EuclideanSpace ℝ (Fin 2)
abbrev E3 := EuclideanSpace ℝ (Fin 3)

theorem sphere_two_null :
    (μH[(2 : ℕ)] : Measure E2) (sphere 0 1) = 0 := by
  exact addHaar_sphere (μH[(2 : ℕ)] : Measure E2) 0 1

theorem sphere_three_null :
    (μH[(3 : ℕ)] : Measure E3) (sphere 0 1) = 0 := by
  exact addHaar_sphere (μH[(3 : ℕ)] : Measure E3) 0 1

#print axioms sphere_two_null
#print axioms sphere_three_null

end ConstructionTargets.LowerDimensionalSphereNullity
