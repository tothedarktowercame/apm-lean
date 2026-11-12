import ConstructionTargets.UpperSemicircleCauchy
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Cauchy's theorem on a circular sector

This file gives the interval-integral boundary expression for the positively
oriented sector with radius `R` and opening angle `α`.  The three terms are
the lower radius, the counterclockwise circular arc, and the upper radius
traversed back toward the origin.
-/

open Complex MeasureTheory Real Set
open scoped Interval

noncomputable section

namespace ConstructionTargets.SectorCauchy

/-- The positively oriented boundary integral of `f` around the circular
sector of radius `R` and opening angle `α`, written as three real interval
integrals. -/
def sectorBoundaryIntegral (f : ℂ → ℂ) (R α : ℝ) : ℂ :=
  (∫ x : ℝ in 0..R, f x) +
    (∫ θ : ℝ in 0..α,
      f (R * Complex.exp (I * θ)) *
        (I * R * Complex.exp (I * θ))) -
    Complex.exp (I * α) *
      ∫ x : ℝ in 0..R, f (x * Complex.exp (I * α))

/-- **Cauchy's theorem for a circular sector.** The positively oriented
boundary integral of an entire function around a sector is zero. -/
theorem sectorBoundaryIntegral_eq_zero
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R α : ℝ) :
    sectorBoundaryIntegral f R α = 0 := by
  obtain ⟨g, hg⟩ := hf.isExactOn_univ
  have hlower (x : ℝ) :
      HasDerivAt (fun t : ℝ => g t) (f x) x := by
    simpa using (hg (x : ℂ) (mem_univ _)).comp_ofReal
  have harc (θ : ℝ) :
      HasDerivAt (fun t : ℝ => g (R * Complex.exp (I * t)))
        (f (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ))) θ := by
    exact UpperSemicircleCauchy.primitive_comp_path_hasDerivAt
      (γ := fun z : ℂ => R * Complex.exp (I * z))
      (hg (R * Complex.exp (I * θ)) (mem_univ _))
      (by
        convert ((hasDerivAt_id (x := (θ : ℂ))).const_mul I).cexp.const_mul (R : ℂ)
          using 1 <;> simp [id_eq] <;> ring)
  have hupper (x : ℝ) :
      HasDerivAt (fun t : ℝ => g (t * Complex.exp (I * α)))
        (f (x * Complex.exp (I * α)) * Complex.exp (I * α)) x := by
    exact UpperSemicircleCauchy.primitive_comp_path_hasDerivAt
      (γ := fun z : ℂ => z * Complex.exp (I * α))
      (hg (x * Complex.exp (I * α)) (mem_univ _))
      (by
        simpa using
          ((hasDerivAt_id (x := (x : ℂ))).mul_const
            (Complex.exp (I * α))))
  have hlower_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) (fun x _ => hlower x)
    ((hf.continuous.comp continuous_ofReal).intervalIntegrable _ _)
  have harc_cont : Continuous (fun θ : ℝ =>
      f (R * Complex.exp (I * θ)) *
        (I * R * Complex.exp (I * θ))) :=
    (hf.continuous.comp (by fun_prop : Continuous fun θ : ℝ =>
      R * Complex.exp (I * θ))).mul
    (by fun_prop : Continuous fun θ : ℝ =>
      I * R * Complex.exp (I * θ))
  have harc_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := α) (fun θ _ => harc θ)
    (harc_cont.intervalIntegrable _ _)
  have hupper_cont : Continuous (fun x : ℝ =>
      f (x * Complex.exp (I * α)) * Complex.exp (I * α)) :=
    (hf.continuous.comp (by fun_prop : Continuous fun x : ℝ =>
      x * Complex.exp (I * α))).mul continuous_const
  have hupper_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) (fun x _ => hupper x)
    (hupper_cont.intervalIntegrable _ _)
  have hupper_int' :
      Complex.exp (I * α) *
          ∫ x : ℝ in 0..R, f (x * Complex.exp (I * α)) =
        g (R * Complex.exp (I * α)) - g 0 := by
    calc
      Complex.exp (I * α) *
          ∫ x : ℝ in 0..R, f (x * Complex.exp (I * α)) =
          ∫ x : ℝ in 0..R,
            Complex.exp (I * α) * f (x * Complex.exp (I * α)) :=
        (intervalIntegral.integral_const_mul
          (a := 0) (b := R) (Complex.exp (I * α))
          (fun x : ℝ => f (x * Complex.exp (I * α)))).symm
      (∫ x : ℝ in 0..R,
          Complex.exp (I * α) * f (x * Complex.exp (I * α))) =
          ∫ x : ℝ in 0..R,
            f (x * Complex.exp (I * α)) * Complex.exp (I * α) := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
      _ = g (R * Complex.exp (I * α)) - g 0 := by
        simpa using hupper_int
  rw [sectorBoundaryIntegral, hlower_int, harc_int]
  rw [hupper_int']
  simp

/-- **Cauchy's theorem on a sector inside an open convex domain.** It is
enough for the function to be holomorphic on an open convex set containing
the three parameterized boundary pieces; it need not be entire. -/
theorem sectorBoundaryIntegral_eq_zero_of_convex
    (f : ℂ → ℂ) (R α : ℝ) (s : Set ℂ)
    (hs : Convex ℝ s) (hso : IsOpen s)
    (hf : DifferentiableOn ℂ f s)
    (hlower : ∀ x ∈ [[(0 : ℝ), R]], (x : ℂ) ∈ s)
    (harc : ∀ θ ∈ [[(0 : ℝ), α]],
      R * Complex.exp (I * θ) ∈ s)
    (hupper : ∀ x ∈ [[(0 : ℝ), R]],
      x * Complex.exp (I * α) ∈ s) :
    sectorBoundaryIntegral f R α = 0 := by
  obtain ⟨g, hg⟩ := hs.exists_forall_hasDerivWithinAt hf
  have hgAt {z : ℂ} (hz : z ∈ s) : HasDerivAt g (f z) z :=
    (hg z hz).hasDerivAt (hso.mem_nhds hz)
  have hlower_deriv (x : ℝ) (hx : x ∈ [[(0 : ℝ), R]]) :
      HasDerivAt (fun t : ℝ => g t) (f x) x := by
    simpa using (hgAt (hlower x hx)).comp_ofReal
  have harc_deriv (θ : ℝ) (hθ : θ ∈ [[(0 : ℝ), α]]) :
      HasDerivAt (fun t : ℝ => g (R * Complex.exp (I * t)))
        (f (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ))) θ := by
    exact UpperSemicircleCauchy.primitive_comp_path_hasDerivAt
      (γ := fun z : ℂ => R * Complex.exp (I * z))
      (hgAt (harc θ hθ))
      (by
        convert ((hasDerivAt_id (x := (θ : ℂ))).const_mul I).cexp.const_mul (R : ℂ)
          using 1 <;> simp [id_eq] <;> ring)
  have hupper_deriv (x : ℝ) (hx : x ∈ [[(0 : ℝ), R]]) :
      HasDerivAt (fun t : ℝ => g (t * Complex.exp (I * α)))
        (f (x * Complex.exp (I * α)) * Complex.exp (I * α)) x := by
    exact UpperSemicircleCauchy.primitive_comp_path_hasDerivAt
      (γ := fun z : ℂ => z * Complex.exp (I * α))
      (hgAt (hupper x hx))
      (by
        simpa using
          ((hasDerivAt_id (x := (x : ℂ))).mul_const
            (Complex.exp (I * α))))
  have hlower_cont : ContinuousOn (fun x : ℝ => f x) [[(0 : ℝ), R]] :=
    hf.continuousOn.comp continuous_ofReal.continuousOn hlower
  have harc_cont : ContinuousOn (fun θ : ℝ =>
      f (R * Complex.exp (I * θ)) *
        (I * R * Complex.exp (I * θ))) [[(0 : ℝ), α]] :=
    (hf.continuousOn.comp
      (by fun_prop : Continuous (fun θ : ℝ =>
        R * Complex.exp (I * θ))).continuousOn harc).mul
      (by fun_prop : Continuous (fun θ : ℝ =>
        I * R * Complex.exp (I * θ))).continuousOn
  have hupper_cont : ContinuousOn (fun x : ℝ =>
      f (x * Complex.exp (I * α)) * Complex.exp (I * α))
      [[(0 : ℝ), R]] :=
    (hf.continuousOn.comp
      (by fun_prop : Continuous (fun x : ℝ =>
        x * Complex.exp (I * α))).continuousOn hupper).mul continuousOn_const
  have hlower_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) hlower_deriv
    (hlower_cont.intervalIntegrable)
  have harc_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := α) harc_deriv
    (harc_cont.intervalIntegrable)
  have hupper_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) hupper_deriv
    (hupper_cont.intervalIntegrable)
  have hupper_int' :
      Complex.exp (I * α) *
          ∫ x : ℝ in 0..R, f (x * Complex.exp (I * α)) =
        g (R * Complex.exp (I * α)) - g 0 := by
    calc
      Complex.exp (I * α) *
          ∫ x : ℝ in 0..R, f (x * Complex.exp (I * α)) =
          ∫ x : ℝ in 0..R,
            Complex.exp (I * α) * f (x * Complex.exp (I * α)) :=
        (intervalIntegral.integral_const_mul
          (a := 0) (b := R) (Complex.exp (I * α))
          (fun x : ℝ => f (x * Complex.exp (I * α)))).symm
      _ = ∫ x : ℝ in 0..R,
            f (x * Complex.exp (I * α)) * Complex.exp (I * α) := by
              apply intervalIntegral.integral_congr
              intro x _
              ring
      _ = g (R * Complex.exp (I * α)) - g 0 := by
        simpa using hupper_int
  rw [sectorBoundaryIntegral, hlower_int, harc_int, hupper_int']
  simp

/-- The boundary integral of the Cauchy kernel around a sector, reduced to
four endpoint values of the principal complex logarithm.  The hypotheses
choose a logarithm branch separately on the lower radius, arc, and upper
radius; this is the explicit winding-number calculation needed for a sector
residue theorem. -/
theorem sectorBoundaryIntegral_sub_inv_eq_log_endpoints
    (R α : ℝ) (a : ℂ)
    (hlower : ∀ x ∈ [[(0 : ℝ), R]], (x : ℂ) - a ∈ Complex.slitPlane)
    (harc : ∀ θ ∈ [[(0 : ℝ), α]],
      R * Complex.exp (I * θ) - a ∈ Complex.slitPlane)
    (hupper : ∀ x ∈ [[(0 : ℝ), R]],
      a - x * Complex.exp (I * α) ∈ Complex.slitPlane) :
    sectorBoundaryIntegral (fun z => (z - a)⁻¹) R α =
      Complex.log (R * Complex.exp (I * α) - a) - Complex.log (-a) +
        Complex.log a - Complex.log (a - R * Complex.exp (I * α)) := by
  have hlower_deriv (x : ℝ) (hx : x ∈ [[(0 : ℝ), R]]) :
      HasDerivAt (fun t : ℝ => Complex.log ((t : ℂ) - a))
        (((x : ℂ) - a)⁻¹) x := by
    convert (((hasDerivAt_id (x := (x : ℂ))).comp_ofReal).sub_const a).clog_real
      (hlower x hx) using 1
    simp
  have harc_deriv (θ : ℝ) (hθ : θ ∈ [[(0 : ℝ), α]]) :
      HasDerivAt
        (fun t : ℝ => Complex.log (R * Complex.exp (I * t) - a))
        ((R * Complex.exp (I * θ) - a)⁻¹ *
          (I * R * Complex.exp (I * θ))) θ := by
    have hp : HasDerivAt (fun t : ℝ => R * Complex.exp (I * t) - a)
        (I * R * Complex.exp (I * θ)) θ := by
      convert (((((hasDerivAt_id (x := (θ : ℂ))).comp_ofReal).const_mul I).cexp.const_mul
        (R : ℂ))).sub_const a
        using 1 <;> simp <;> ring
    convert hp.clog_real (harc θ hθ) using 1
    field_simp
  have hupper_deriv (x : ℝ) (hx : x ∈ [[(0 : ℝ), R]]) :
      HasDerivAt
        (fun t : ℝ => Complex.log (a - t * Complex.exp (I * α)))
        ((x * Complex.exp (I * α) - a)⁻¹ * Complex.exp (I * α)) x := by
    have hp : HasDerivAt (fun t : ℝ => a - t * Complex.exp (I * α))
        (-Complex.exp (I * α)) x := by
      convert (hasDerivAt_const (x := x) a).sub
        (((hasDerivAt_id (x := (x : ℂ))).comp_ofReal).mul_const
          (Complex.exp (I * α))) using 1 <;>
          simp
    convert hp.clog_real (hupper x hx) using 1
    rw [div_eq_mul_inv]
    rw [show a - x * Complex.exp (I * α) =
      -(x * Complex.exp (I * α) - a) by ring, inv_neg]
    ring
  have hlower_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) - a)⁻¹)
      [[(0 : ℝ), R]] := by
    exact ContinuousOn.inv₀
      (continuous_ofReal.sub continuous_const).continuousOn
      (fun x hx => Complex.slitPlane_ne_zero (hlower x hx))
  have harc_cont : ContinuousOn (fun θ : ℝ =>
      (R * Complex.exp (I * θ) - a)⁻¹ *
        (I * R * Complex.exp (I * θ))) [[(0 : ℝ), α]] := by
    apply ContinuousOn.mul
    · exact ContinuousOn.inv₀
        ((by fun_prop : Continuous fun θ : ℝ =>
          R * Complex.exp (I * θ) - a).continuousOn)
        (fun θ hθ => Complex.slitPlane_ne_zero (harc θ hθ))
    · fun_prop
  have hupper_cont : ContinuousOn (fun x : ℝ =>
      (x * Complex.exp (I * α) - a)⁻¹ * Complex.exp (I * α))
      [[(0 : ℝ), R]] := by
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀
        ((by fun_prop : Continuous fun x : ℝ =>
          x * Complex.exp (I * α) - a).continuousOn)
      intro x hx hzero
      have : a - x * Complex.exp (I * α) = 0 := by
        rw [sub_eq_zero] at hzero ⊢
        exact hzero.symm
      exact Complex.slitPlane_ne_zero (hupper x hx) this
    · fun_prop
  have hlower_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) hlower_deriv hlower_cont.intervalIntegrable
  have harc_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := α) harc_deriv harc_cont.intervalIntegrable
  have hupper_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) hupper_deriv hupper_cont.intervalIntegrable
  rw [sectorBoundaryIntegral, hlower_int, harc_int]
  have hmul : Complex.exp (I * α) *
      (∫ x : ℝ in 0..R, (x * Complex.exp (I * α) - a)⁻¹) =
      ∫ x : ℝ in 0..R,
        (x * Complex.exp (I * α) - a)⁻¹ * Complex.exp (I * α) := by
    calc
      _ = ∫ x : ℝ in 0..R,
          Complex.exp (I * α) *
            (x * Complex.exp (I * α) - a)⁻¹ :=
        (intervalIntegral.integral_const_mul
          (a := 0) (b := R) (Complex.exp (I * α))
          (fun x : ℝ => (x * Complex.exp (I * α) - a)⁻¹)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
  rw [hmul, hupper_int]
  simp
  ring

end ConstructionTargets.SectorCauchy
