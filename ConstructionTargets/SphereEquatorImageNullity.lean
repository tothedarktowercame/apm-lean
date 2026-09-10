import ConstructionTargets.LowerDimensionalSphereNullity
import ConstructionTargets.SphereEquatorEmbedding
import Mathlib.Geometry.Euclidean.Volume.Measure

noncomputable section
namespace ConstructionTargets.SphereEquatorImageNullity
open MeasureTheory MeasureTheory.Measure Metric
open ConstructionTargets.SphereEquatorEmbedding
open scoped MeasureTheory RealInnerProductSpace
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev EA (d : ℕ) := EuclideanSpace ℝ (Fin (d + 1))

def equator (d : ℕ) : Set (EA d) :=
  {y | y ∈ sphere 0 1 ∧ y (Fin.last d) = 0}

def dropLast (d : ℕ) (y : EA d) : E d :=
  WithLp.toLp 2 (fun i : Fin d => y i.castSucc)

@[simp] theorem appendZero_dropLast {d : ℕ} {y : EA d}
    (hy : y (Fin.last d) = 0) : appendZero d (dropLast d y) = y := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hy.symm
  · simp [dropLast]

theorem image_sphere (d : ℕ) :
    appendZero d '' sphere (0 : E d) 1 = equator d := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨?_, appendZero_last d x⟩
    simpa [mem_sphere, (appendZero d).norm_map] using hx
  · rintro ⟨hy, hlast⟩
    refine ⟨dropLast d y, ?_, appendZero_dropLast hlast⟩
    have hn : ‖dropLast d y‖ = ‖y‖ := by
      rw [← (appendZero d).norm_map]
      rw [appendZero_dropLast hlast]
    simpa [mem_sphere, hn] using hy

theorem equator_measure_eq_zero (d : ℕ)
    (hsource : (μH[(d : ℕ)] : Measure (E d)) (sphere 0 1) = 0) :
    (μH[(d : ℕ)] : Measure (EA d)) (equator d) = 0 := by
  rw [← image_sphere]
  rw [(appendZero d).isometry.hausdorffMeasure_image (Or.inl (by positivity))]
  exact hsource

example (h : (μH[(2 : ℕ)] : Measure (E 2)) (sphere 0 1) = 0) :
    (μH[(2 : ℕ)] : Measure (EA 2)) (equator 2) = 0 :=
  equator_measure_eq_zero 2 h

example (h : (μH[(3 : ℕ)] : Measure (E 3)) (sphere 0 1) = 0) :
    (μH[(3 : ℕ)] : Measure (EA 3)) (equator 3) = 0 :=
  equator_measure_eq_zero 3 h

#print axioms appendZero_dropLast
#print axioms image_sphere
#print axioms equator_measure_eq_zero
end ConstructionTargets.SphereEquatorImageNullity
