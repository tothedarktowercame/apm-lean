import ConstructionTargets.PeriodicCircleHomotopyWinding
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Periodic real-line winding adapter for t97J08

This file constructs the real-line lift and the seam-compatible linear
homotopy to its standard winding loop.  It keeps the values in `Circle`; the
frozen complex-valued predicate can obtain the corresponding complex values by
the subtype coercion.
-/

namespace ConstructionTargets.T97J08PeriodicWindingAdapter

open ConstructionTargets.CircleWindingUniqueness

noncomputable abbrev period : ℝ := 2 * Real.pi

/-- Periodicity in the parametrization used by frozen `t97J08`. -/
def IsPeriodic (g : ℝ → Circle) : Prop :=
  ∀ t, g (t + period) = g t

/-- A chosen real argument of the initial circle value. -/
noncomputable def baseAngle (g : C(ℝ, Circle)) : ℝ :=
  (Circle.surjOn_exp_neg_pi_pi (Set.mem_univ (g 0))).choose

theorem exp_baseAngle (g : C(ℝ, Circle)) :
    Circle.exp (baseAngle g) = g 0 :=
  (Circle.surjOn_exp_neg_pi_pi (Set.mem_univ (g 0))).choose_spec.2

/-- The unique global lift of a circle-valued real-line path with the chosen
initial argument. -/
noncomputable def globalLift (g : C(ℝ, Circle)) : C(ℝ, ℝ) :=
  (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    g 0 (baseAngle g) (exp_baseAngle g)).choose

theorem globalLift_zero (g : C(ℝ, Circle)) :
    globalLift g 0 = baseAngle g :=
  (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    g 0 (baseAngle g) (exp_baseAngle g)).choose_spec.1.1

theorem exp_globalLift (g : C(ℝ, Circle)) (t : ℝ) :
    Circle.exp (globalLift g t) = g t :=
  congr_fun (Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    g 0 (baseAngle g) (exp_baseAngle g)).choose_spec.1.2 t

/-- The unique winding integer read from one period of the global lift. -/
theorem existsUnique_periodWinding (g : C(ℝ, Circle)) (hg : IsPeriodic g) :
    ∃! n : ℤ, IsEndpointWinding (globalLift g period) (globalLift g 0) n := by
  apply (exp_eq_iff_existsUnique_endpointWinding _ _).mp
  rw [exp_globalLift, exp_globalLift]
  simpa [IsPeriodic] using hg 0

noncomputable def winding (g : C(ℝ, Circle)) (hg : IsPeriodic g) : ℤ :=
  (existsUnique_periodWinding g hg).choose

theorem winding_spec (g : C(ℝ, Circle)) (hg : IsPeriodic g) :
    IsEndpointWinding (globalLift g period) (globalLift g 0) (winding g hg) :=
  (existsUnique_periodWinding g hg).choose_spec.1

/-- The lift changes by exactly its integral winding displacement at every
period seam, not merely at the chosen initial seam. -/
theorem globalLift_add_period (g : C(ℝ, Circle)) (hg : IsPeriodic g) (t : ℝ) :
    globalLift g (t + period) =
      globalLift g t + (winding g hg : ℝ) * period := by
  let d : ℝ → ℝ := fun x ↦ globalLift g (x + period) - globalLift g x
  have hdcont : Continuous d :=
    ((globalLift g).continuous.comp (continuous_id.add continuous_const)).sub
      (globalLift g).continuous
  have hdconst : d t = d 0 := by
    apply Circle.isCoveringMap_exp.const_of_comp hdcont
    intro x y
    rw [Circle.exp_sub, Circle.exp_sub]
    rw [exp_globalLift, exp_globalLift, exp_globalLift, exp_globalLift,
      hg x, hg y]
    simp
  have hs := winding_spec g hg
  unfold IsEndpointWinding at hs
  dsimp [d] at hdconst
  rw [globalLift_zero] at hs hdconst
  norm_num at hdconst
  change globalLift g (2 * Real.pi) =
    baseAngle g + (winding g hg : ℝ) * (2 * Real.pi) at hs
  rw [hs] at hdconst
  dsimp [period] at hdconst ⊢
  linarith

/-- The straight-line interpolation in lift coordinates. -/
noncomputable def homotopyAngle (g : C(ℝ, Circle)) (hg : IsPeriodic g)
    (t s : ℝ) : ℝ :=
  (1 - s) * globalLift g t + s * (winding g hg : ℝ) * t

theorem homotopyAngle_add_period (g : C(ℝ, Circle)) (hg : IsPeriodic g)
    (t s : ℝ) :
    homotopyAngle g hg (t + period) s =
      homotopyAngle g hg t s + (winding g hg : ℝ) * period := by
  rw [homotopyAngle, homotopyAngle, globalLift_add_period g hg]
  ring

/-- The explicit periodic homotopy from `g` to its standard winding loop. -/
noncomputable def periodicHomotopy (g : C(ℝ, Circle)) (hg : IsPeriodic g)
    (t s : ℝ) : Circle :=
  Circle.exp (homotopyAngle g hg t s)

theorem continuous_periodicHomotopy (g : C(ℝ, Circle)) (hg : IsPeriodic g) :
    Continuous (fun p : ℝ × ℝ ↦ periodicHomotopy g hg p.1 p.2) := by
  apply Circle.exp.continuous.comp
  unfold homotopyAngle
  fun_prop

theorem periodicHomotopy_periodic (g : C(ℝ, Circle)) (hg : IsPeriodic g)
    (t s : ℝ) :
    periodicHomotopy g hg (t + period) s = periodicHomotopy g hg t s := by
  unfold periodicHomotopy
  rw [homotopyAngle_add_period g hg]
  apply Circle.exp_eq_exp.mpr
  exact ⟨winding g hg, by simp [period]⟩

theorem periodicHomotopy_zero (g : C(ℝ, Circle)) (hg : IsPeriodic g) (t : ℝ) :
    periodicHomotopy g hg t 0 = g t := by
  simp [periodicHomotopy, homotopyAngle, exp_globalLift]

theorem periodicHomotopy_one (g : C(ℝ, Circle)) (hg : IsPeriodic g) (t : ℝ) :
    periodicHomotopy g hg t 1 = Circle.exp ((winding g hg : ℝ) * t) := by
  simp [periodicHomotopy, homotopyAngle]

#print axioms exp_globalLift
#print axioms existsUnique_periodWinding
#print axioms globalLift_add_period
#print axioms continuous_periodicHomotopy
#print axioms periodicHomotopy_periodic

end ConstructionTargets.T97J08PeriodicWindingAdapter
