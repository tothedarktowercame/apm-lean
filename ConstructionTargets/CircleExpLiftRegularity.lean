import ConstructionTargets.ContinuousLiftLocalInverseRegularity
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Regularity of continuous lifts through the circle exponential

A continuous real lift of a `C^n` circle-valued map is itself `C^n`.  The
local scalar coordinate is the imaginary part after rotation by the value of
the lift at the point under consideration.
-/

open scoped Topology

noncomputable section

namespace ConstructionTargets.CircleExpLiftRegularity

open ConstructionTargets.ContinuousLiftLocalInverseRegularity

/-- The rotated imaginary coordinate on the real parameter line. -/
private def rotatedImaginaryCoordinate (a r : ℝ) : ℝ :=
  (Complex.exp (-Complex.I * a) * Complex.exp (Complex.I * r)).im

/-- The rotated imaginary coordinate of a circle-valued map. -/
private def rotatedCircleCoordinate (a : ℝ) (g : ℝ → Circle) (t : ℝ) : ℝ :=
  (Complex.exp (-Complex.I * a) * (g t : ℂ)).im

private theorem rotatedImaginaryCoordinate_eq (a r : ℝ) :
    rotatedImaginaryCoordinate a r = Real.sin (r - a) := by
  unfold rotatedImaginaryCoordinate
  rw [show -Complex.I * (a : ℂ) = ((-a : ℝ) : ℂ) * Complex.I by
    push_cast
    ring]
  rw [Complex.exp_mul_I, show Complex.I * (r : ℂ) = (r : ℂ) * Complex.I by ring,
    Complex.exp_mul_I]
  have hcos (s : ℝ) : (Complex.cos (s : ℂ)).re = Real.cos s := by
    rw [← Complex.ofReal_cos]
    exact Complex.ofReal_re _
  have hsin (s : ℝ) : (Complex.sin (s : ℂ)).re = Real.sin s := by
    rw [← Complex.ofReal_sin]
    exact Complex.ofReal_re _
  simp [Complex.mul_re, Complex.mul_im, Real.sin_sub, hcos, hsin]
  ring

private theorem hasDerivAt_rotatedImaginaryCoordinate (a : ℝ) :
    HasDerivAt (rotatedImaginaryCoordinate a) 1 a := by
  rw [show rotatedImaginaryCoordinate a = fun r ↦ Real.sin (r - a) by
    funext r
    exact rotatedImaginaryCoordinate_eq a r]
  have hsub : HasDerivAt (fun r : ℝ ↦ r - a) 1 a :=
    (hasDerivAt_id a).sub_const a
  simpa only [sub_self, Real.cos_zero, one_mul] using hsub.sin

/-- A continuous lift through `Circle.exp` inherits the differentiability of
the circle-valued map. -/
theorem contDiff_circleExp_lift
    {n : WithTop ℕ∞} (hn : n ≠ 0)
    (g : ℝ → Circle) (theta : C(ℝ, ℝ))
    (hg : ContDiff ℝ n (fun t ↦ (g t : ℂ)))
    (hlift : ∀ t, Circle.exp (theta t) = g t) :
    ContDiff ℝ n theta := by
  rw [contDiff_iff_contDiffAt]
  intro x
  let a := theta x
  let phi : ℝ → ℝ := rotatedImaginaryCoordinate a
  let u : ℝ → ℝ := rotatedCircleCoordinate a g
  have hphi : ContDiffAt ℝ n phi (theta x) := by
    rw [show phi = fun r ↦ Real.sin (r - a) by
      funext r
      exact rotatedImaginaryCoordinate_eq a r]
    fun_prop
  have hphi' : HasDerivAt phi 1 (theta x) := by
    simpa [a, phi] using hasDerivAt_rotatedImaginaryCoordinate a
  have hu : ContDiffAt ℝ n u x := by
    exact (Complex.imCLM.contDiff.comp
      (contDiff_const.mul hg)).contDiffAt
  have hcomp : phi ∘ theta = u := by
    funext t
    simp only [Function.comp_apply, phi, u, rotatedImaginaryCoordinate,
      rotatedCircleCoordinate]
    rw [← hlift t]
    simp only [Circle.coe_exp]
    rw [mul_comm Complex.I (theta t : ℂ)]
  exact contDiffAt_of_continuous_lift hn theta.continuous.continuousAt
    hu hphi hphi' one_ne_zero hcomp

#print axioms contDiff_circleExp_lift

end ConstructionTargets.CircleExpLiftRegularity
