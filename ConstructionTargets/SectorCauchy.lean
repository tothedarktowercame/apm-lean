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

/-- Integrability of an integrand on each of the three parameterized sides
of a circular sector. -/
def SectorBoundaryIntegrable (f : ℂ → ℂ) (R α : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f x) volume 0 R ∧
    IntervalIntegrable (fun θ : ℝ =>
      f (R * Complex.exp (I * θ)) *
        (I * R * Complex.exp (I * θ))) volume 0 α ∧
    IntervalIntegrable (fun x : ℝ =>
      f (x * Complex.exp (I * α))) volume 0 R

/-- Sector boundary integration is additive for integrable boundary data. -/
lemma sectorBoundaryIntegral_add
    {f g : ℂ → ℂ} {R α : ℝ}
    (hf : SectorBoundaryIntegrable f R α)
    (hg : SectorBoundaryIntegrable g R α) :
    sectorBoundaryIntegral (fun z => f z + g z) R α =
      sectorBoundaryIntegral f R α + sectorBoundaryIntegral g R α := by
  unfold sectorBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1]
  rw [show (fun θ : ℝ =>
      (f (R * Complex.exp (I * θ)) + g (R * Complex.exp (I * θ))) *
        (I * R * Complex.exp (I * θ))) =
      (fun θ : ℝ =>
        f (R * Complex.exp (I * θ)) * (I * R * Complex.exp (I * θ)) +
        g (R * Complex.exp (I * θ)) * (I * R * Complex.exp (I * θ))) by
      funext θ; ring]
  rw [intervalIntegral.integral_add hf.2.1 hg.2.1]
  rw [intervalIntegral.integral_add hf.2.2 hg.2.2]
  ring

/-- Constants pull through a sector boundary integral. -/
lemma sectorBoundaryIntegral_const_mul (c : ℂ) (f : ℂ → ℂ) (R α : ℝ) :
    sectorBoundaryIntegral (fun z => c * f z) R α =
      c * sectorBoundaryIntegral f R α := by
  have hlower :
      (∫ x : ℝ in 0..R, c * f x) =
        c * ∫ x : ℝ in 0..R, f x := by
    exact intervalIntegral.integral_const_mul (μ := volume)
      (a := (0 : ℝ)) (b := R) c (fun x : ℝ => f x)
  have harc :
      (∫ θ : ℝ in 0..α,
        c * f (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ))) =
        c * ∫ θ : ℝ in 0..α,
          f (R * Complex.exp (I * θ)) *
            (I * R * Complex.exp (I * θ)) := by
    rw [show (fun θ : ℝ =>
        c * f (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ))) =
        (fun θ : ℝ => c *
          (f (R * Complex.exp (I * θ)) *
            (I * R * Complex.exp (I * θ)))) by funext θ; ring]
    exact intervalIntegral.integral_const_mul (μ := volume)
      (a := (0 : ℝ)) (b := α) c (fun θ : ℝ =>
        f (R * Complex.exp (I * θ)) *
          (I * R * Complex.exp (I * θ)))
  have hupper :
      (∫ x : ℝ in 0..R,
        c * f (x * Complex.exp (I * α))) =
        c * ∫ x : ℝ in 0..R,
          f (x * Complex.exp (I * α)) := by
    exact intervalIntegral.integral_const_mul (μ := volume)
      (a := (0 : ℝ)) (b := R) c (fun x : ℝ =>
        f (x * Complex.exp (I * α)))
  unfold sectorBoundaryIntegral
  rw [hlower, harc, hupper]
  ring

/-- Boundary integrals around a sector respect pointwise equality on its
three parameterized sides. -/
lemma sectorBoundaryIntegral_congr
    {f g : ℂ → ℂ} {R α : ℝ}
    (hlower : ∀ x ∈ [[(0 : ℝ), R]], f x = g x)
    (harc : ∀ θ ∈ [[(0 : ℝ), α]],
      f (R * Complex.exp (I * θ)) = g (R * Complex.exp (I * θ)))
    (hupper : ∀ x ∈ [[(0 : ℝ), R]],
      f (x * Complex.exp (I * α)) = g (x * Complex.exp (I * α))) :
    sectorBoundaryIntegral f R α = sectorBoundaryIntegral g R α := by
  have h₁ := intervalIntegral.integral_congr (μ := volume) hlower
  have h₂ : (∫ θ : ℝ in 0..α,
      f (R * Complex.exp (I * θ)) * (I * R * Complex.exp (I * θ))) =
      ∫ θ : ℝ in 0..α,
        g (R * Complex.exp (I * θ)) * (I * R * Complex.exp (I * θ)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change f (R * Complex.exp (I * θ)) * _ =
      g (R * Complex.exp (I * θ)) * _
    rw [harc θ hθ]
  have h₃ := intervalIntegral.integral_congr (μ := volume) hupper
  unfold sectorBoundaryIntegral
  rw [h₁, h₂, h₃]

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

/-- Across the negative-real-axis branch cut, the principal logarithms of
`z` and `-z` differ by `π i` when `z` is in the upper half-plane. -/
lemma log_sub_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log z - Complex.log (-z) = π * I := by
  rw [Complex.log, Complex.log, norm_neg,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]
  push_cast
  ring

/-- The sector Cauchy kernel has winding number one when the pole and the
translated terminal arc point lie in the upper half-plane and the three
displayed logarithm branches are valid. -/
theorem sectorBoundaryIntegral_sub_inv_eq_two_pi_I
    (R α : ℝ) (a : ℂ)
    (hlower : ∀ x ∈ [[(0 : ℝ), R]], (x : ℂ) - a ∈ Complex.slitPlane)
    (harc : ∀ θ ∈ [[(0 : ℝ), α]],
      R * Complex.exp (I * θ) - a ∈ Complex.slitPlane)
    (hupper : ∀ x ∈ [[(0 : ℝ), R]],
      a - x * Complex.exp (I * α) ∈ Complex.slitPlane)
    (ha_im : 0 < a.im)
    (hend_im : 0 < (R * Complex.exp (I * α) - a).im) :
    sectorBoundaryIntegral (fun z => (z - a)⁻¹) R α = 2 * π * I := by
  rw [sectorBoundaryIntegral_sub_inv_eq_log_endpoints R α a hlower harc hupper]
  have h₁ := log_sub_log_neg_of_im_pos hend_im
  have h₂ := log_sub_log_neg_of_im_pos ha_im
  rw [show a - R * Complex.exp (I * α) =
    -(R * Complex.exp (I * α) - a) by ring]
  rw [show -a = -(a) by rfl]
  linear_combination h₁ + h₂

/-- A unit-winding evaluation when the outer arc crosses the principal
logarithm cut once.  Splitting the arc at `β` and using `log (z-a)` before
the crossing and `log (a-z)` afterwards records the branch jump explicitly. -/
theorem sectorBoundaryIntegral_sub_inv_eq_two_pi_I_of_split_arc
    (R α β : ℝ) (a : ℂ)
    (hlower : ∀ x ∈ [[(0 : ℝ), R]], (x : ℂ) - a ∈ Complex.slitPlane)
    (harc₁ : ∀ θ ∈ [[(0 : ℝ), β]],
      R * Complex.exp (I * θ) - a ∈ Complex.slitPlane)
    (harc₂ : ∀ θ ∈ [[β, α]],
      a - R * Complex.exp (I * θ) ∈ Complex.slitPlane)
    (hupper : ∀ x ∈ [[(0 : ℝ), R]],
      a - x * Complex.exp (I * α) ∈ Complex.slitPlane)
    (ha_im : 0 < a.im)
    (hmid_im : 0 < (R * Complex.exp (I * β) - a).im) :
    sectorBoundaryIntegral (fun z => (z - a)⁻¹) R α = 2 * π * I := by
  let v : ℝ → ℂ := fun θ => I * R * Complex.exp (I * θ)
  let w : ℝ → ℂ := fun θ => R * Complex.exp (I * θ) - a
  have hlower_deriv (x : ℝ) (hx : x ∈ [[(0 : ℝ), R]]) :
      HasDerivAt (fun t : ℝ => Complex.log ((t : ℂ) - a))
        (((x : ℂ) - a)⁻¹) x := by
    convert (((hasDerivAt_id (x := (x : ℂ))).comp_ofReal).sub_const a).clog_real
      (hlower x hx) using 1
    simp
  have harc₁_deriv (θ : ℝ) (hθ : θ ∈ [[(0 : ℝ), β]]) :
      HasDerivAt (fun t : ℝ => Complex.log (w t))
        ((w θ)⁻¹ * v θ) θ := by
    have hp : HasDerivAt w (v θ) θ := by
      dsimp [w, v]
      convert (((((hasDerivAt_id (x := (θ : ℂ))).comp_ofReal).const_mul I).cexp.const_mul
        (R : ℂ))).sub_const a using 1 <;> simp <;> ring
    convert hp.clog_real (harc₁ θ hθ) using 1
    field_simp
  have harc₂_deriv (θ : ℝ) (hθ : θ ∈ [[β, α]]) :
      HasDerivAt (fun t : ℝ => Complex.log (-w t))
        ((w θ)⁻¹ * v θ) θ := by
    have hp : HasDerivAt (fun t : ℝ => -w t) (-v θ) θ := by
      dsimp [w, v]
      convert (((((hasDerivAt_id (x := (θ : ℂ))).comp_ofReal).const_mul I).cexp.const_mul
        (R : ℂ))).sub_const a |>.neg using 1 <;> simp <;> ring
    have hs : -w θ = a - R * Complex.exp (I * θ) := by
      dsimp [w]
      ring
    convert hp.clog_real (hs ▸ harc₂ θ hθ) using 1
    rw [div_eq_mul_inv]
    rw [show -w θ = -(w θ) by rfl, inv_neg]
    ring
  have hupper_deriv (x : ℝ) (hx : x ∈ [[(0 : ℝ), R]]) :
      HasDerivAt
        (fun t : ℝ => Complex.log (a - t * Complex.exp (I * α)))
        ((x * Complex.exp (I * α) - a)⁻¹ * Complex.exp (I * α)) x := by
    have hp : HasDerivAt (fun t : ℝ => a - t * Complex.exp (I * α))
        (-Complex.exp (I * α)) x := by
      convert (hasDerivAt_const (x := x) a).sub
        (((hasDerivAt_id (x := (x : ℂ))).comp_ofReal).mul_const
          (Complex.exp (I * α))) using 1 <;> simp
    convert hp.clog_real (hupper x hx) using 1
    rw [div_eq_mul_inv]
    rw [show a - x * Complex.exp (I * α) =
      -(x * Complex.exp (I * α) - a) by ring, inv_neg]
    ring
  have hlower_cont : ContinuousOn (fun x : ℝ => ((x : ℂ) - a)⁻¹)
      [[(0 : ℝ), R]] := ContinuousOn.inv₀
    (continuous_ofReal.sub continuous_const).continuousOn
    (fun x hx => Complex.slitPlane_ne_zero (hlower x hx))
  have harc₁_cont : ContinuousOn (fun θ : ℝ => (w θ)⁻¹ * v θ) [[(0 : ℝ), β]] := by
    apply ContinuousOn.mul
    · exact ContinuousOn.inv₀
        ((by fun_prop : Continuous w).continuousOn)
        (fun θ hθ => Complex.slitPlane_ne_zero (harc₁ θ hθ))
    · exact (by fun_prop : Continuous v).continuousOn
  have harc₂_cont : ContinuousOn (fun θ : ℝ => (w θ)⁻¹ * v θ) [[β, α]] := by
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀ ((by fun_prop : Continuous w).continuousOn)
      intro θ hθ hw0
      apply Complex.slitPlane_ne_zero (harc₂ θ hθ)
      dsimp [w] at hw0 ⊢
      linear_combination -hw0
    · exact (by fun_prop : Continuous v).continuousOn
  have hupper_cont : ContinuousOn (fun x : ℝ =>
      (x * Complex.exp (I * α) - a)⁻¹ * Complex.exp (I * α))
      [[(0 : ℝ), R]] := by
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀
        ((by fun_prop : Continuous fun x : ℝ =>
          x * Complex.exp (I * α) - a).continuousOn)
      intro x hx hzero
      apply Complex.slitPlane_ne_zero (hupper x hx)
      rw [sub_eq_zero] at hzero ⊢
      exact hzero.symm
    · fun_prop
  have hlower_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) hlower_deriv hlower_cont.intervalIntegrable
  have harc₁_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := β) harc₁_deriv harc₁_cont.intervalIntegrable
  have harc₂_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := β) (b := α) harc₂_deriv harc₂_cont.intervalIntegrable
  have harc_int : (∫ θ : ℝ in 0..α, (w θ)⁻¹ * v θ) =
      (Complex.log (w β) - Complex.log (w 0)) +
        (Complex.log (-w α) - Complex.log (-w β)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      harc₁_cont.intervalIntegrable harc₂_cont.intervalIntegrable,
      harc₁_int, harc₂_int]
  have hupper_int := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := R) hupper_deriv hupper_cont.intervalIntegrable
  have hmul : Complex.exp (I * α) *
      (∫ x : ℝ in 0..R, (x * Complex.exp (I * α) - a)⁻¹) =
      ∫ x : ℝ in 0..R,
        (x * Complex.exp (I * α) - a)⁻¹ * Complex.exp (I * α) := by
    calc
      _ = ∫ x : ℝ in 0..R,
          Complex.exp (I * α) * (x * Complex.exp (I * α) - a)⁻¹ :=
        (intervalIntegral.integral_const_mul
          (a := 0) (b := R) (Complex.exp (I * α))
          (fun x : ℝ => (x * Complex.exp (I * α) - a)⁻¹)).symm
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
  rw [sectorBoundaryIntegral, hlower_int]
  change _ + (∫ θ : ℝ in 0..α, (w θ)⁻¹ * v θ) - _ = _
  rw [harc_int, hmul, hupper_int]
  have hmid := log_sub_log_neg_of_im_pos hmid_im
  have ha := log_sub_log_neg_of_im_pos ha_im
  dsimp [w]
  simp
  rw [show a - R * Complex.exp (I * β) =
    -(R * Complex.exp (I * β) - a) by ring]
  linear_combination hmid + ha

end ConstructionTargets.SectorCauchy
