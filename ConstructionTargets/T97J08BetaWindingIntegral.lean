import Mathlib
import ConstructionTargets.T97J08FrozenWindingWiring
import ConstructionTargets.ExplicitCrossDerivativeCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The frozen beta integral and the lifted winding

The algebraic and FTC portions of the winding-integral comparison are proved
here.  The final theorem isolates one regularity fact about the covering lift:
the current covering-space API constructs it only as a `ContinuousMap`, while
the integral calculation needs that lift to be `C¹`.
-/

open MeasureTheory Set

namespace ConstructionTargets.T97J08BetaWindingIntegral

open ConstructionTargets.T97J08FrozenWindingWiring
open ConstructionTargets.T97J08PeriodicWindingAdapter

noncomputable section

abbrev beta := ConstructionTargets.ExplicitCrossDerivativeCalculus.beta

def betaIntegral (f : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, beta (f t) (deriv f t)

/-- Radial motion cancels from the angle form; tangential speed is all that
remains.  This is the pointwise calculation used after differentiating a
polar lift. -/
theorem beta_radial_tangent (q : ℂ) (r r' theta' : ℝ) (hr : r ≠ 0)
    (hq : q.re ^ 2 + q.im ^ 2 = 1) :
    beta ((r : ℂ) * q)
      ((r' : ℂ) * q + (r : ℂ) * ((theta' : ℂ) * Complex.I * q)) =
      theta' / (2 * Real.pi) := by
  unfold beta
  unfold ConstructionTargets.ExplicitCrossDerivativeCalculus.beta
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  field_simp [hr, Real.pi_ne_zero]
  nlinarith

/-- Exact analytic seam left by Mathlib's continuous covering lift. -/
def LiftIsCOne (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f) : Prop :=
  ContDiff ℝ 1 (globalLift (circleLoop f hf))

theorem betaIntegral_eq_winding_of_liftIsCOne
    (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f)
    (hlift : LiftIsCOne f hf) :
    betaIntegral f =
      (winding (circleLoop f hf) (circleLoop_periodic f hf) : ℝ) := by
  let theta : ℝ → ℝ := globalLift (circleLoop f hf)
  have htheta : ContDiff ℝ 1 theta := hlift
  have hpolar : f = fun t ↦ (‖f t‖ : ℂ) * Complex.exp (Complex.I * theta t) := by
    funext t
    have he := congrArg Subtype.val
      (exp_globalLift (circleLoop f hf) t)
    change Complex.exp ((theta t : ℂ) * Complex.I) = normalizedLoop f t at he
    rw [mul_comm] at he
    rw [he]
    unfold normalizedLoop
    have hn : ((‖f t‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hf.2.2 t))
    field_simp [hn]
  have hintegrand : ∀ t, beta (f t) (deriv f t) = deriv theta t / (2 * Real.pi) := by
    intro t
    have hf_diff : DifferentiableAt ℝ f t := hf.1.differentiable (by simp) t
    have hrho : DifferentiableAt ℝ (fun x ↦ ‖f x‖) t := hf_diff.norm ℝ (hf.2.2 t)
    have htheta_t : DifferentiableAt ℝ theta t :=
      htheta.differentiable (by norm_num) t
    let theta' : ℝ := deriv theta t
    have htheta_c : HasDerivAt (fun x ↦ (theta x : ℂ)) (theta' : ℂ) t :=
      htheta_t.hasDerivAt.ofReal_comp
    have hq : HasDerivAt (fun x ↦ Complex.exp (Complex.I * theta x))
        ((theta' : ℂ) * Complex.I *
          Complex.exp (Complex.I * theta t)) t := by
      have hcR : HasDerivAt (fun x ↦ Real.cos (theta x))
          (-Real.sin (theta t) * theta') t :=
        (Real.hasDerivAt_cos (theta t)).comp t htheta_t.hasDerivAt
      have hsR : HasDerivAt (fun x ↦ Real.sin (theta x))
          (Real.cos (theta t) * theta') t :=
        (Real.hasDerivAt_sin (theta t)).comp t htheta_t.hasDerivAt
      have htrig := hcR.ofReal_comp.add (hsR.ofReal_comp.mul_const Complex.I)
      convert htrig using 1
      · funext x
        rw [show Complex.I * (theta x : ℂ) = (theta x : ℂ) * Complex.I by ring,
          Complex.exp_mul_I]
        simp
      · rw [show Complex.I * (theta t : ℂ) = (theta t : ℂ) * Complex.I by ring,
          Complex.exp_mul_I]
        rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
        ring_nf
        rw [show Complex.I ^ 2 = (-1 : ℂ) by norm_num]
        push_cast
        ring
    let rho' : ℝ := deriv (fun x ↦ ‖f x‖) t
    have hp : HasDerivAt
        (fun x ↦ (‖f x‖ : ℂ) * Complex.exp (Complex.I * theta x))
        ((rho' : ℂ) *
            Complex.exp (Complex.I * theta t) +
          (‖f t‖ : ℂ) * ((theta' : ℂ) * Complex.I *
            Complex.exp (Complex.I * theta t))) t := by
      have hrho_c : HasDerivAt (fun x ↦ (‖f x‖ : ℂ))
          (rho' : ℂ) t :=
        hrho.hasDerivAt.ofReal_comp
      exact hrho_c.mul hq
    rw [hpolar]
    rw [hp.deriv]
    apply beta_radial_tangent (Complex.exp (Complex.I * theta t))
      ‖f t‖ rho' (deriv theta t)
      (norm_ne_zero_iff.mpr (hf.2.2 t))
    rw [show (Complex.exp (Complex.I * theta t)).re ^ 2 +
        (Complex.exp (Complex.I * theta t)).im ^ 2 =
        Complex.normSq (Complex.exp (Complex.I * theta t)) by
      simp [Complex.normSq_apply, pow_two]]
    simp [Complex.normSq_eq_norm_sq]
  unfold betaIntegral
  simp_rw [hintegrand]
  rw [intervalIntegral.integral_div]
  have hFTC : ∫ t in (0 : ℝ)..2 * Real.pi, deriv theta t =
      theta (2 * Real.pi) - theta 0 := by
    apply intervalIntegral.integral_deriv_eq_sub
    · intro t ht
      exact htheta.differentiable (by norm_num) t
    · exact (htheta.continuous_deriv (by norm_num)).intervalIntegrable _ _
  rw [hFTC]
  have hperiod := globalLift_add_period (circleLoop f hf)
    (circleLoop_periodic f hf) 0
  change theta (0 + period) = theta 0 +
    (winding (circleLoop f hf) (circleLoop_periodic f hf) : ℝ) * period at hperiod
  simp only [zero_add] at hperiod
  dsimp [period] at hperiod
  rw [hperiod]
  field_simp [Real.pi_ne_zero]
  ring

theorem winding_eq_betaIntegral_of_liftIsCOne
    (f : ℝ → ℂ) (hf : SmoothPuncturedLoop f)
    (n : ℤ) (hn : FrozenWindingNumber f n)
    (hlift : LiftIsCOne f hf) :
    (n : ℝ) = betaIntegral f := by
  rw [betaIntegral_eq_winding_of_liftIsCOne f hf hlift]
  exact_mod_cast frozenWindingNumber_unique f hf hn

#print axioms beta_radial_tangent
#print axioms betaIntegral_eq_winding_of_liftIsCOne
#print axioms winding_eq_betaIntegral_of_liftIsCOne

end

end ConstructionTargets.T97J08BetaWindingIntegral
