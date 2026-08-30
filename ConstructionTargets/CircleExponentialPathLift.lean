import ConstructionTargets.CircleWindingUniqueness
import Mathlib.Topology.Homotopy.Lifting

/-!
# Path lifting through the circle exponential

This file applies Mathlib's covering-map instance for `Circle.exp` to a
circle-valued path.  The resulting lift starts at a prescribed real number,
projects pointwise to the original path, and, for a loop, has a uniquely
determined integral endpoint displacement.
-/

open scoped unitInterval

namespace ConstructionTargets.CircleExponentialPathLift

open ConstructionTargets.CircleWindingUniqueness

/-- The canonical lift of a circle-valued path through `Circle.exp`, starting
at the prescribed real lift of its left endpoint. -/
noncomputable def lift (gamma : C(I, Circle)) (a : ℝ)
    (h0 : gamma 0 = Circle.exp a) : C(I, ℝ) :=
  Circle.isCoveringMap_exp.liftPath gamma a h0

/-- The canonical lift has the prescribed initial value. -/
theorem lift_zero (gamma : C(I, Circle)) (a : ℝ)
    (h0 : gamma 0 = Circle.exp a) :
    lift gamma a h0 0 = a :=
  Circle.isCoveringMap_exp.liftPath_zero gamma a h0

/-- Exponentiating the canonical lift recovers the original path pointwise. -/
theorem exp_lift (gamma : C(I, Circle)) (a : ℝ)
    (h0 : gamma 0 = Circle.exp a) (t : I) :
    Circle.exp (lift gamma a h0 t) = gamma t :=
  congr_fun (Circle.isCoveringMap_exp.liftPath_lifts gamma a h0) t

/-- In particular, the exponential of the lifted right endpoint is the right
endpoint of the original circle path. -/
theorem exp_lift_one (gamma : C(I, Circle)) (a : ℝ)
    (h0 : gamma 0 = Circle.exp a) :
    Circle.exp (lift gamma a h0 1) = gamma 1 :=
  exp_lift gamma a h0 1

/-- If the original path is closed, the two real endpoints of its lift have
the same circle exponential. -/
theorem exp_lift_one_eq_start (gamma : C(I, Circle)) (a : ℝ)
    (h0 : gamma 0 = Circle.exp a) (hloop : gamma 1 = gamma 0) :
    Circle.exp (lift gamma a h0 1) = Circle.exp a := by
  rw [exp_lift_one gamma a h0, hloop, h0]

/-- A closed circle path, together with a chosen lift of its initial point,
has a unique integral endpoint winding displacement.  Existence comes from
the covering-space lift above; uniqueness is the arithmetic theorem in
`CircleWindingUniqueness`. -/
theorem existsUnique_endpointWinding (gamma : C(I, Circle)) (a : ℝ)
    (h0 : gamma 0 = Circle.exp a) (hloop : gamma 1 = gamma 0) :
    ∃! n : ℤ, IsEndpointWinding (lift gamma a h0 1) a n :=
  (exp_eq_iff_existsUnique_endpointWinding _ _).mp
    (exp_lift_one_eq_start gamma a h0 hloop)

#print axioms lift_zero
#print axioms exp_lift
#print axioms exp_lift_one_eq_start
#print axioms existsUnique_endpointWinding

end ConstructionTargets.CircleExponentialPathLift
