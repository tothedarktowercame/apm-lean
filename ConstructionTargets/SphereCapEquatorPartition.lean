import ConstructionTargets.SphereCapEuclideanImage
import Mathlib.Geometry.Euclidean.Volume.Measure

noncomputable section
namespace ConstructionTargets.SphereCapEquatorPartition

open Metric Set MeasureTheory
open ConstructionTargets.SphereCapEuclideanImage

abbrev EA (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

def equator (d : ℕ) : Set (EA d) :=
  {y | y ∈ sphere 0 1 ∧ y (Fin.last d) = 0}

theorem measurable_strictUpperCap (d : ℕ) : MeasurableSet (strictUpperCap d) := by
  exact isClosed_sphere.measurableSet.inter
    (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ _)).measurableSet

theorem measurable_strictLowerCap (d : ℕ) : MeasurableSet (strictLowerCap d) := by
  exact isClosed_sphere.measurableSet.inter
    (isOpen_lt (PiLp.continuous_apply 2 _ _) continuous_const).measurableSet

theorem measurable_equator (d : ℕ) : MeasurableSet (equator d) := by
  exact isClosed_sphere.measurableSet.inter
    (isClosed_eq (PiLp.continuous_apply 2 _ _) continuous_const).measurableSet

theorem disjoint_upper_lower (d : ℕ) :
    Disjoint (strictUpperCap d) (strictLowerCap d) := by
  rw [Set.disjoint_left]
  intro y hyu hyl
  exact (not_lt_of_ge (le_of_lt hyu.2)) hyl.2

theorem disjoint_upper_equator (d : ℕ) :
    Disjoint (strictUpperCap d) (equator d) := by
  rw [Set.disjoint_left]
  intro y hyu hye
  simpa [hye.2] using hyu.2

theorem disjoint_lower_equator (d : ℕ) :
    Disjoint (strictLowerCap d) (equator d) := by
  rw [Set.disjoint_left]
  intro y hyl hye
  simpa [hye.2] using hyl.2

theorem sphere_partition (d : ℕ) :
    sphere (0 : EA d) 1 = strictUpperCap d ∪ strictLowerCap d ∪ equator d := by
  ext y
  constructor
  · intro hy
    rcases lt_trichotomy (y (Fin.last d)) 0 with hn | hz | hp
    · exact Or.inl (Or.inr ⟨hy, hn⟩)
    · exact Or.inr ⟨hy, hz⟩
    · exact Or.inl (Or.inl ⟨hy, hp⟩)
  · intro hy
    rcases hy with hy | hy
    · rcases hy with hy | hy
      · exact hy.1
      · exact hy.1
    · exact hy.1

example : sphere (0 : EA 2) 1 = strictUpperCap 2 ∪ strictLowerCap 2 ∪ equator 2 :=
  sphere_partition 2

example : sphere (0 : EA 3) 1 = strictUpperCap 3 ∪ strictLowerCap 3 ∪ equator 3 :=
  sphere_partition 3

#print axioms measurable_strictUpperCap
#print axioms measurable_strictLowerCap
#print axioms measurable_equator
#print axioms disjoint_upper_lower
#print axioms disjoint_upper_equator
#print axioms disjoint_lower_equator
#print axioms sphere_partition

end ConstructionTargets.SphereCapEquatorPartition
