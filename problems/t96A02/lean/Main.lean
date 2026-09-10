import Mathlib
import ConstructionTargets.StatementSurfaceModels

/-! # t96A02: fixed points on the wedge of two real projective planes

Both planes are concrete disk quotients with boundary word `aa`; the wedge
identifies the images of their centers and carries the coinduced topology.
The full printed assertion is stated below. Lefschetz theory is a possible
proof dependency, not a prerequisite for expressing fixed points.
-/

open ConstructionTargets.StatementSurfaceModels

theorem apm_t96a02 :
    ∀ f : ContinuousMap ProjectivePlaneWedge ProjectivePlaneWedge, ∃ x, f x = x := by
  sorry
