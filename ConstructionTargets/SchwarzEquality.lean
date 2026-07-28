import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

open Metric Set

noncomputable section

namespace ConstructionTargets.SchwarzEquality

/-- Equality in Schwarz's lemma, in the form that identifies the map with its
derivative times the argument throughout the unit disk. -/
theorem eqOn_deriv_mul
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0)
    (heq : ‖deriv h 0‖ = 1) :
    EqOn h (fun z ↦ deriv h 0 * z) (ball 0 1) := by
  have hh_maps_closed : MapsTo h (ball 0 1) (closedBall (h 0) 1) := by
    intro z hz
    rw [hh_zero]
    exact ball_subset_closedBall (hh_maps hz)
  have hzero : (0 : ℂ) ∈ ball 0 1 := mem_ball_self (by norm_num)
  have hslope : ‖dslope h 0 0‖ = (1 : ℝ) / 1 := by
    simpa using heq
  have haffine :=
    Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div
      hh hh_maps_closed hzero hslope
  intro z hz
  simpa [hh_zero, mul_comm] using haffine hz

/-- Pointwise form of `eqOn_deriv_mul`. -/
theorem eq_deriv_mul
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0)
    (heq : ‖deriv h 0‖ = 1)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    h z = deriv h 0 * z :=
  eqOn_deriv_mul hh hh_maps hh_zero heq hz

/-- Coefficient form of the equality case: a disk self-map with extremal
derivative is multiplication by a unit complex number. -/
theorem exists_unit_mul
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0)
    (heq : ‖deriv h 0‖ = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ z ∈ ball (0 : ℂ) 1, h z = c * z :=
  ⟨deriv h 0, heq, fun _ hz ↦ eq_deriv_mul hh hh_maps hh_zero heq hz⟩

/-- Rotation form of the equality case, matching the statements used by the
subordination and image-domain developments. -/
theorem exists_rotation
    {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 1))
    (hh_maps : MapsTo h (ball 0 1) (ball 0 1))
    (hh_zero : h 0 = 0)
    (heq : ‖deriv h 0‖ = 1) :
    ∃ α : ℝ, ∀ z ∈ ball (0 : ℂ) 1,
      h z = Complex.exp (Complex.I * (α : ℂ)) * z := by
  refine ⟨(deriv h 0).arg, fun z hz ↦ ?_⟩
  rw [eq_deriv_mul hh hh_maps hh_zero heq hz]
  congr 1
  rw [mul_comm]
  simpa [heq] using (Complex.norm_mul_exp_arg_mul_I (deriv h 0)).symm

end ConstructionTargets.SchwarzEquality
