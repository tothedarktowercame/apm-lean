import Mathlib

/-!
# APM t94J05

## Statement repairs

None.

## Encoding questions

The source torus is the actual product of two circles and the target is the
unit `3`-sphere in Euclidean `ℝ⁴`.  Mathlib does not expose a convenient
single smooth-map predicate between these particular embedded-manifold
instances, so smoothness is isolated as a typed predicate on the genuine
continuous map.  Homotopy is Mathlib's native continuous-map homotopy.
-/

open scoped ContDiff

abbrev apm_t94J05_Torus := Circle × Circle
abbrev apm_t94J05_R4 := EuclideanSpace ℝ (Fin 4)
abbrev apm_t94J05_S3 := Metric.sphere (0 : apm_t94J05_R4) 1

/-- The point `(0,0,0,1)` on the unit three-sphere. -/
noncomputable def apm_t94J05_northPole : apm_t94J05_S3 :=
  ⟨EuclideanSpace.single (3 : Fin 4) 1, by simp⟩

/-- Smoothness of a map between the embedded torus and three-sphere. -/
opaque apm_t94J05_IsSmooth (f : C(apm_t94J05_Torus, apm_t94J05_S3)) : Prop

theorem apm_t94j05
    (f : C(apm_t94J05_Torus, apm_t94J05_S3))
    (hf : apm_t94J05_IsSmooth f) :
    ContinuousMap.Homotopic f
      (ContinuousMap.const apm_t94J05_Torus apm_t94J05_northPole) := by
  sorry
