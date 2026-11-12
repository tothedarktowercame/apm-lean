import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Cauchy's theorem on an upper semicircle

This file gives the interval-integral form of the contour identity for the
positively oriented boundary of an upper half-disk.  It is deliberately stated
in the parameterization used by APM contour computations: the diameter runs
from `-R` to `R`, and the arc is `R * exp (I * θ)`, `0 ≤ θ ≤ π`.
-/

open Complex MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ConstructionTargets.UpperSemicircleCauchy

/-- The derivative of a primitive composed with a real-parameterized complex
path is the complex integrand times the velocity of the path. -/
lemma primitive_comp_path_hasDerivAt
    {f g γ : ℂ → ℂ} {γ' : ℂ} {t : ℝ}
    (hg : HasDerivAt g (f (γ t)) (γ t))
    (hγ : HasDerivAt γ γ' t) :
    HasDerivAt (fun s : ℝ => g (γ s)) (f (γ t) * γ') t := by
  exact (hg.comp (t : ℂ) hγ).comp_ofReal

/-- **Cauchy's theorem for an upper semicircle.** If `f` is entire, then the
integral on the diameter from `-R` to `R` plus the counterclockwise arc
integral is zero. -/
theorem intervalIntegral_add_upperSemicircle_eq_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R : ℝ) :
    (∫ x : ℝ in -R..R, f x) +
      ∫ θ : ℝ in 0..π,
        f (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ)) = 0 := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hline (x : ℝ) :
      HasDerivAt (fun t : ℝ => g t) (f x) x := by
    simpa using (hg (x : ℂ) (mem_univ _)).comp_ofReal
  have harc (θ : ℝ) :
      HasDerivAt (fun t : ℝ => g (R * Complex.exp (I * t)))
        (f (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ))) θ := by
    exact primitive_comp_path_hasDerivAt
      (γ := fun z : ℂ => R * Complex.exp (I * z))
      (hg (R * Complex.exp (I * θ)) (mem_univ _))
      (by
        convert ((hasDerivAt_id (x := (θ : ℂ))).const_mul I).cexp.const_mul (R : ℂ) using 1 <;>
          simp [id_eq] <;> ring)
  have hline_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := -R) (b := R)
    (fun x _ => hline x)
    ((hf.continuous.comp continuous_ofReal).intervalIntegrable _ _)
  have harc_cont : Continuous (fun θ : ℝ =>
      f (R * Complex.exp (I * θ)) *
        (I * R * Complex.exp (I * θ))) :=
    (hf.continuous.comp (by fun_prop : Continuous fun θ : ℝ =>
      R * Complex.exp (I * θ))).mul
    (by fun_prop : Continuous fun θ : ℝ =>
      I * R * Complex.exp (I * θ))
  have harc_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := π)
    (fun θ _ => harc θ)
    (harc_cont.intervalIntegrable _ _)
  rw [hline_int, harc_int]
  rw [show I * (π : ℂ) = (π : ℂ) * I by ring, Complex.exp_pi_mul_I]
  simp

end ConstructionTargets.UpperSemicircleCauchy
