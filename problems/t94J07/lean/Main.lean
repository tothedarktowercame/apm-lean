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
  sorry
