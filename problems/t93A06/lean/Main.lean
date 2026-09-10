import Mathlib
import ConstructionTargets.TorusFormTargets

/-! # t93A06: descent, primitive and periods of the printed torus form
The torus is the coordinatewise real quotient by the integer lattice. Its
smooth atlas must make the actual quotient projection a local diffeomorphism.
The integral uses the oriented fundamental square; the path integral uses all
four printed edges in order. The primitive is an explicit alternating 1-form.
-/
open scoped Manifold ContDiff
open ConstructionTargets.ManifoldFormTargets ConstructionTargets.TorusFormTargets
noncomputable section

theorem apm_t93a06 : ∃ atlas : SmoothAtlas,
    letI := atlas.charts
    (∀ x y : Plane, projection x = projection y ↔
      ∃ k : Fin 2 → ℤ, ∀ i, y i = x i + (k i : ℝ)) ∧
    (∃ form : Form Plane Torus 2,
      IsSmooth form ∧ pullback projection form = sourceForm ∧
      (∀ other : Form Plane Torus 2, IsSmooth other →
        pullback projection other = sourceForm → other = form) ∧
      torusIntegral form = 1 / 4 ∧ ¬ IsExact form) ∧
    IsSmooth primitive ∧ exteriorDerivative primitive = sourceForm ∧
    parallelogramIntegral primitive = 1 / 4 := by
  sorry
