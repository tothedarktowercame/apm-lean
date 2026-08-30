import ConstructionTargets.CircleExpLiftRegularity
import ConstructionTargets.T97J08FrozenWindingWiring
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smoothness of the frozen t97J08 normalized loop and its global lift

This file connects the frozen smooth punctured-loop hypothesis to the generic
regularity theorem for continuous lifts through `Circle.exp`.  It does not use
the beta-integral identity.
-/

open scoped Topology

noncomputable section

namespace ConstructionTargets.T97J08SmoothLiftRegularity

open ConstructionTargets

/-- The complex coercion of the frozen normalized circle loop is `C¹`.

The denominator is treated explicitly as a complex-valued smooth function.
Its nonvanishing follows from the pointwise punctured-loop hypothesis. -/
theorem circleLoop_coe_contDiff_one
    (f : ℝ → ℂ)
    (hf : T97J08FrozenWindingWiring.SmoothPuncturedLoop f) :
    ContDiff ℝ 1
      (fun t ↦ ((T97J08FrozenWindingWiring.circleLoop f hf t : Circle) : ℂ)) := by
  have hf_one : ContDiff ℝ 1 f := hf.1.of_le (by norm_num)
  have hnorm : ContDiff ℝ 1 (fun t ↦ ‖f t‖) :=
    hf_one.norm ℂ hf.2.2
  have hnorm_complex : ContDiff ℝ 1 (fun t ↦ (‖f t‖ : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hnorm
  have hnorm_ne : ∀ t, (‖f t‖ : ℂ) ≠ 0 := by
    intro t
    exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf.2.2 t))
  change ContDiff ℝ 1 (fun t ↦ f t / (‖f t‖ : ℂ))
  simpa only [div_eq_mul_inv] using
    hf_one.mul (hnorm_complex.inv hnorm_ne)

/-- The exact frozen-loop specialization: the chosen global real lift through
`Circle.exp` is `C¹`. -/
theorem globalLift_circleLoop_contDiff_one
    (f : ℝ → ℂ)
    (hf : T97J08FrozenWindingWiring.SmoothPuncturedLoop f) :
    ContDiff ℝ 1
      (T97J08PeriodicWindingAdapter.globalLift
        (T97J08FrozenWindingWiring.circleLoop f hf)) := by
  apply CircleExpLiftRegularity.contDiff_circleExp_lift one_ne_zero
    (T97J08FrozenWindingWiring.circleLoop f hf)
    (T97J08PeriodicWindingAdapter.globalLift
      (T97J08FrozenWindingWiring.circleLoop f hf))
  · exact circleLoop_coe_contDiff_one f hf
  · exact T97J08PeriodicWindingAdapter.exp_globalLift
      (T97J08FrozenWindingWiring.circleLoop f hf)

#print axioms circleLoop_coe_contDiff_one
#print axioms globalLift_circleLoop_contDiff_one

end ConstructionTargets.T97J08SmoothLiftRegularity
