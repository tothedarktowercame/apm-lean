import Mathlib
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# APM t94J07 — homotopy invariance of a closed-form integral

The theorem is stated for the concrete compact boundaryless manifolds
`X = Y = S¹`.  A map of the circle is represented by a smooth ambient map
`ℝ² → ℝ²` that preserves the unit circle, and a smooth homotopy is represented
the same way.  The pullback integral is the genuine interval integral obtained
by evaluating an alternating one-form on the derivative of the parametrized
circle.

## Statement repairs

The source writes `∂X = φ`; this is read as the standard `∂X = ∅`.

Because Mathlib presently has no general integration and Stokes theory for
manifold differential forms, the source's general compact manifolds are
specialized to the concrete case `S¹ → S¹`.  This retains the closed form,
smooth homotopy, derivative pullback, and integral whose invariance is to be
proved, without assuming a Stokes or homotopy-invariance law.

## Encoding questions

Extending this statement from the circle to arbitrary oriented compact
boundaryless manifolds awaits a general manifold differential-form integration
API in Mathlib.
-/

open MeasureTheory Set
open scoped Interval

noncomputable section

abbrev T94J07E2 := EuclideanSpace ℝ (Fin 2)
abbrev T94J07Form1 := T94J07E2 → T94J07E2 [⋀^Fin 1]→L[ℝ] ℝ

def t94J07CirclePoint (θ : ℝ) : T94J07E2 :=
  EuclideanSpace.single 0 (Real.cos θ) +
    EuclideanSpace.single 1 (Real.sin θ)

def t94J07CircleVelocity (θ : ℝ) : T94J07E2 :=
  EuclideanSpace.single 0 (-Real.sin θ) +
    EuclideanSpace.single 1 (Real.cos θ)

lemma t94J07CirclePoint_norm (θ : ℝ) : ‖t94J07CirclePoint θ‖ = 1 := by
  have hsq : ‖t94J07CirclePoint θ‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [t94J07CirclePoint, Fin.sum_univ_succ]
  have hn : 0 ≤ ‖t94J07CirclePoint θ‖ := norm_nonneg _
  nlinarith

lemma t94J07CircleVelocity_tangent (θ : ℝ) :
    inner ℝ (t94J07CirclePoint θ) (t94J07CircleVelocity θ) = 0 := by
  rw [PiLp.inner_apply]
  simp [t94J07CirclePoint, t94J07CircleVelocity, Fin.sum_univ_succ]
  rw [real_inner_comm (Real.sin θ) (Real.cos θ)]
  ring

lemma t94J07CirclePoint_two_pi :
    t94J07CirclePoint (2 * Real.pi) = t94J07CirclePoint 0 := by
  ext i
  fin_cases i <;> simp [t94J07CirclePoint]

lemma t94J07CircleVelocity_two_pi :
    t94J07CircleVelocity (2 * Real.pi) = t94J07CircleVelocity 0 := by
  ext i
  fin_cases i <;> simp [t94J07CircleVelocity]

/-- A smooth ambient representative of a smooth self-map of the unit circle. -/
def t94J07IsSmoothCircleMap (f : T94J07E2 → T94J07E2) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧
    ∀ x : T94J07E2, ‖x‖ = 1 → ‖f x‖ = 1

/-- A smooth ambient homotopy through self-maps of the unit circle. -/
def t94J07IsSmoothCircleHomotopy
    (f g : T94J07E2 → T94J07E2)
    (H : T94J07E2 × ℝ → T94J07E2) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) H ∧
    (∀ x : T94J07E2, H (x, 0) = f x) ∧
    (∀ x : T94J07E2, H (x, 1) = g x) ∧
    ∀ (x : T94J07E2) (t : ℝ), ‖x‖ = 1 → t ∈ Icc (0 : ℝ) 1 →
      ‖H (x, t)‖ = 1

/-- Closedness after restriction to the circle: the exterior derivative
vanishes on pairs of vectors tangent to `S¹`. -/
def t94J07IsClosedOnCircle (alpha : T94J07Form1) : Prop :=
  ∀ (x : T94J07E2), ‖x‖ = 1 →
    ∀ v : Fin 2 → T94J07E2,
      (∀ i : Fin 2, inner ℝ x (v i) = 0) → extDeriv alpha x v = 0

/-- Integral over `S¹` of the pullback of `alpha` by `f`, using the standard
counterclockwise parametrization and the actual Fréchet derivative of `f`. -/
def t94J07PullbackCircleIntegral
    (alpha : T94J07Form1) (f : T94J07E2 → T94J07E2) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    alpha (f (t94J07CirclePoint θ))
      (fun _ ↦ fderiv ℝ f (t94J07CirclePoint θ) (t94J07CircleVelocity θ))

def t94J07PullbackCircleIntegrand
    (alpha : T94J07Form1) (f : T94J07E2 → T94J07E2) (θ : ℝ) : ℝ :=
  alpha (f (t94J07CirclePoint θ))
    (fun _ ↦ fderiv ℝ f (t94J07CirclePoint θ) (t94J07CircleVelocity θ))

/-- Periodicity holds for the complete frozen pullback integrand, including
both the evaluation point and the derivative applied to its velocity. -/
lemma t94J07PullbackCircleIntegrand_two_pi
    (alpha : T94J07Form1) (f : T94J07E2 → T94J07E2) :
    t94J07PullbackCircleIntegrand alpha f (2 * Real.pi) =
      t94J07PullbackCircleIntegrand alpha f 0 := by
  simp only [t94J07PullbackCircleIntegrand, t94J07CirclePoint_two_pi,
    t94J07CircleVelocity_two_pi]

lemma t94J07HomotopySliceIntegrand_two_pi
    (alpha : T94J07Form1) (H : T94J07E2 × ℝ → T94J07E2) (t : ℝ) :
    t94J07PullbackCircleIntegrand alpha (fun x ↦ H (x, t)) (2 * Real.pi) =
      t94J07PullbackCircleIntegrand alpha (fun x ↦ H (x, t)) 0 :=
  t94J07PullbackCircleIntegrand_two_pi alpha (fun x ↦ H (x, t))

/-- The interval FTC turns periodic endpoint equality into the exact
vanishing needed for the mixed `θ`-derivative term in the cylinder proof. -/
lemma t94J07_integral_deriv_eq_zero_of_periodic
    (q : ℝ → ℝ) (hq : ContDiff ℝ 1 q)
    (hperiod : q (2 * Real.pi) = q 0) :
    ∫ θ in (0 : ℝ)..2 * Real.pi, deriv q θ = 0 := by
  rw [intervalIntegral.integral_deriv_eq_sub
    (fun x _ => hq.differentiable one_ne_zero x)
    ((hq.continuous_deriv le_rfl).intervalIntegrable 0 (2 * Real.pi))]
  linarith

theorem apm_t94j07
    (alpha : T94J07Form1)
    (halpha_smooth : ContDiff ℝ (⊤ : ℕ∞) alpha)
    (halpha_closed : t94J07IsClosedOnCircle alpha)
    (f g : T94J07E2 → T94J07E2)
    (hf : t94J07IsSmoothCircleMap f)
    (hg : t94J07IsSmoothCircleMap g)
    (H : T94J07E2 × ℝ → T94J07E2)
    (hH : t94J07IsSmoothCircleHomotopy f g H) :
    t94J07PullbackCircleIntegral alpha f =
      t94J07PullbackCircleIntegral alpha g := by
  /-
  CLOSER HOP 2 (2026-08-08): the concrete parameter geometry needed by a direct cylinder
  proof is now compiled above. `t94J07CirclePoint_norm` proves the path lies
  on the unit circle, `t94J07CircleVelocity_tangent` proves its velocity is
  tangent, and `t94J07CirclePoint_two_pi` records the periodic endpoint
  cancellation.

  Desk research covered `LEMMA-INDEX.md`, every `ConstructionTargets/`
  module, the solved and partial differential-form siblings (`t00J04`,
  `t01J06`, `t02A05`, `t94A10`, `t98A05`), Mathlib's differential-form,
  parametric-integral, interval-FTC, and integration-by-parts sources, and git
  history.  `extDeriv_pullback` supplies the relevant local chain-rule
  identity, while `integral_deriv_of_contDiffOn_Icc` and the parametric
  integral differentiation theorems supply separate analytic pieces.  No
  theorem combines them into homotopy invariance of this line integral.

  A local completion must bundle the slice
  `x ↦ H (x,t)`, identify its `fderiv` with the frozen integrand, differentiate
  the resulting θ-integral in `t`, use `extDeriv_pullback` plus
  `halpha_closed` after proving both partial derivatives of `H` are tangent by
  differentiating the unit-norm constraint, and convert the remaining mixed
  term into a θ-derivative whose integral vanishes by the compiled periodic
  endpoint equality. Going beyond hop 1, `t94J07CircleVelocity_two_pi` and
  `t94J07PullbackCircleIntegrand_two_pi` now prove periodicity of the complete
  frozen integrand, including the derivative applied to the velocity;
  `t94J07HomotopySliceIntegrand_two_pi` specializes it uniformly to every
  homotopy slice. Thus the eventual θ-FTC boundary cancellation is fully
  compiled rather than inferred only from point periodicity.

  The remaining local completion still requires the dominated/continuous
  parameter-integral hypotheses and both interval FTC applications.  The
  frozen statement is unchanged; no axiom or opaque placeholder was added.

  CLOSER HOP 3 (2026-08-08): one of those FTC applications is now closed as
  `t94J07_integral_deriv_eq_zero_of_periodic`.  For any `C¹` scalar primitive,
  it feeds global differentiability and interval-integrability of the
  derivative to `intervalIntegral.integral_deriv_eq_sub`, then uses endpoint
  periodicity to obtain the exact zero integral.  Together with the hop-2
  endpoint equality, the eventual mixed `θ`-derivative cancellation now has
  no remaining FTC or boundary arithmetic obligation. Attempts to have
  `fun_prop` synthesize smoothness of the circle parametrization exposed a
  missing rule for `PiLp.single`; it must be bundled manually through
  `lp.singleContinuousLinearMap` before the larger parametric calculation.
  The remaining bridge is differentiating the homotopy-slice integral,
  deriving the closed-form/mixed-derivative identity, and supplying its
  domination/continuity hypotheses. The frozen statement is unchanged.
  -/
  sorry
