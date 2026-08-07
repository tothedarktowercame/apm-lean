import Mathlib

/-!
# APM a03J07 — Phragmén–Lindelöf on the upper half-plane

## Statement repairs

The source's boundary hypothesis quantifies `x ∈ ℝ` but writes `|f(z)|`;
the free `z` is corrected to `x`, as required by the intended real-axis
boundary bound.

## Encoding questions

None. The open upper half-plane, its closure, boundedness, continuity, and
complex differentiability are represented directly.
-/

open Set

noncomputable section

def apm_a03J07_H : Set ℂ := {z : ℂ | 0 < z.im}

theorem apm_a03j07 (f : ℂ → ℂ) (M C0 : ℝ)
    (hcont : ContinuousOn f (closure apm_a03J07_H))
    (hanal : DifferentiableOn ℂ f apm_a03J07_H)
    (hbdd : ∀ z ∈ closure apm_a03J07_H, ‖f z‖ ≤ C0)
    (hreal : ∀ x : ℝ, ‖f (x : ℂ)‖ ≤ M) :
    ∀ z ∈ apm_a03J07_H, ‖f z‖ ≤ M := by
  sorry
