import Mathlib

/-!
# APM a95A08 — length of a univalent image of the unit circle

## Statement repairs

None.

## Encoding questions

None. The disk, its image domain, the parametrized boundary curve, and its
arc length are defined directly. Analyticity on a neighborhood of the closed
disk is represented by differentiability on a strictly larger closed disk.
-/

open Complex Metric Set Real MeasureTheory
open scoped Interval Topology

noncomputable section

def apm_a95A08_Delta : Set ℂ := ball 0 1

def apm_a95A08_imageDomain (f : ℂ → ℂ) : Set ℂ :=
  f '' apm_a95A08_Delta

def apm_a95A08_boundaryCurve (f : ℂ → ℂ) (θ : ℝ) : ℂ :=
  f (Complex.exp (Complex.I * (θ : ℂ)))

def apm_a95A08_curveLength (f : ℂ → ℂ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    ‖deriv f (Complex.exp (Complex.I * (θ : ℂ)))‖

theorem apm_a95a08 (f : ℂ → ℂ)
    (hf_holo : ∃ ε > 0,
      DifferentiableOn ℂ f (closedBall 0 (1 + ε)))
    (hf_inj : Set.InjOn f (closedBall 0 1))
    (hf_zero : f 0 = 0)
    (hf_deriv : ‖deriv f 0‖ = 1) :
    2 * Real.pi ≤ apm_a95A08_curveLength f ∧
    (2 * Real.pi < apm_a95A08_curveLength f →
      ¬(apm_a95A08_Delta ⊆ apm_a95A08_imageDomain f)) := by
  sorry
