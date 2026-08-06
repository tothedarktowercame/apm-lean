import Mathlib

/-! # APM t97J08: the angle form and winding number

## Statement repairs

None.

## Encoding question

Mathlib does not yet bundle exterior differentiation and integration of
differential forms on smooth manifolds.  The printed one-form is represented
faithfully by its evaluation on a point and tangent vector in `ℂ ≃ ℝ²`;
closedness is retained as a typed predicate on such one-forms.  A smooth map
from `S¹` is represented by its smooth, `2π`-periodic parametrization, and its
circle integral is the corresponding interval integral.  The degree defining
the winding number is retained as an integer-valued typed operation.
-/

open MeasureTheory
open scoped ContDiff

noncomputable section

abbrev t97J08OneForm := ℂ → ℂ → ℝ

/-- `β = (x dy - y dx) / (2π(x²+y²))`, evaluated on a tangent vector. -/
def t97J08Beta : t97J08OneForm := fun z v ↦
  (z.re * v.im - z.im * v.re) /
    (2 * Real.pi * (z.re ^ 2 + z.im ^ 2))

def IsT97J08ClosedOneFormOnPuncturedPlane
    (eta : t97J08OneForm) : Prop := by sorry

def IsT97J08SmoothPuncturedLoop (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧
  (∀ t : ℝ, f (t + 2 * Real.pi) = f t) ∧
  ∀ t : ℝ, f t ≠ 0

/-- The degree of `t ↦ f(t) / ‖f(t)‖`, hence the winding number about `0`. -/
def t97J08WindingNumber (f : ℝ → ℂ) : ℤ := by sorry

def t97J08BetaIntegral (f : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, t97J08Beta (f t) (deriv f t)

theorem apm_t97j08 :
    IsT97J08ClosedOneFormOnPuncturedPlane t97J08Beta ∧
    ∀ f : ℝ → ℂ, IsT97J08SmoothPuncturedLoop f →
      (t97J08WindingNumber f : ℝ) = t97J08BetaIntegral f := by
  sorry
