import Mathlib
import ConstructionTargets.Surfaces

open ConstructionTargets.Surfaces

/-- In the old realization, the orientable genus-zero polygon identifies no
boundary points at all; it is the closed disk, not the two-sphere. -/
example (x y : Disk) : ¬ SurfaceRel true 0 x y := by
  simp [SurfaceRel]

