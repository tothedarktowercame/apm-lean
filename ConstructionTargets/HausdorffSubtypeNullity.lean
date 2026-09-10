import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Hausdorff

open MeasureTheory MeasureTheory.Measure
open scoped MeasureTheory ENNReal

namespace ConstructionTargets.HausdorffSubtypeNullity

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem subtype_univ_measure (d : ℝ) (hd : 0 ≤ d) (s : Set X) :
    (μH[d] : Measure s) Set.univ = (μH[d] : Measure X) s := by
  have h := isometry_subtype_coe.hausdorffMeasure_image (d := d) (Or.inl hd)
    (Set.univ : Set s)
  simpa using h.symm

theorem subtype_univ_null {d : ℝ} (hd : 0 ≤ d) {s : Set X}
    (hs : (μH[d] : Measure X) s = 0) :
    (μH[d] : Measure s) Set.univ = 0 := by
  rw [subtype_univ_measure d hd s, hs]

example {s : Set (EuclideanSpace ℝ (Fin 3))}
    (hs : (μH[(2 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 3))) s = 0) :
    (μH[(2 : ℕ)] : Measure s) Set.univ = 0 := by
  exact subtype_univ_null (d := (2 : ℕ)) (by norm_num) hs

example {s : Set (EuclideanSpace ℝ (Fin 4))}
    (hs : (μH[(3 : ℕ)] : Measure (EuclideanSpace ℝ (Fin 4))) s = 0) :
    (μH[(3 : ℕ)] : Measure s) Set.univ = 0 := by
  exact subtype_univ_null (d := (3 : ℕ)) (by norm_num) hs

#print axioms subtype_univ_measure
#print axioms subtype_univ_null

end ConstructionTargets.HausdorffSubtypeNullity
