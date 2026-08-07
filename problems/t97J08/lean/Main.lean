import Mathlib

/-! # APM t97J08: the angle form and winding number

## Statement repairs

None.

## Encoding question

The printed one-form is represented by evaluation on a point and tangent
vector in `ℂ ≃ ℝ²`. Closedness is the concrete coordinate exterior-derivative
equation. A smooth map from `S¹` is a smooth `2π`-periodic parametrization.
Its degree is encoded without a placeholder: `n` is its winding number when
the normalized loop is homotopic through periodic unit-circle loops to
`t ↦ exp (i n t)`.
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
    (eta : t97J08OneForm) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    DifferentiableAt ℝ (fun w : ℂ ↦ eta w 1) z ∧
    DifferentiableAt ℝ (fun w : ℂ ↦ eta w Complex.I) z ∧
    (fderiv ℝ (fun w : ℂ ↦ eta w Complex.I) z) 1 =
      (fderiv ℝ (fun w : ℂ ↦ eta w 1) z) Complex.I

def IsT97J08SmoothPuncturedLoop (f : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧
  (∀ t : ℝ, f (t + 2 * Real.pi) = f t) ∧
  ∀ t : ℝ, f t ≠ 0

def t97J08NormalizedLoop (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  f t / ‖f t‖

/-- A concrete periodic homotopy witnessing that the normalized loop has
degree `n`. -/
def IsT97J08WindingNumber (f : ℝ → ℂ) (n : ℤ) : Prop :=
  ∃ H : ℝ → ℝ → ℂ,
    Continuous (fun p : ℝ × ℝ ↦ H p.1 p.2) ∧
    (∀ t s : ℝ, H (t + 2 * Real.pi) s = H t s) ∧
    (∀ t : ℝ, H t 0 = t97J08NormalizedLoop f t) ∧
    (∀ t : ℝ, H t 1 = Complex.exp (Complex.I * (n : ℝ) * t)) ∧
    ∀ t s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ‖H t s‖ = 1

def t97J08BetaIntegral (f : ℝ → ℂ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi, t97J08Beta (f t) (deriv f t)

theorem apm_t97j08 :
    IsT97J08ClosedOneFormOnPuncturedPlane t97J08Beta ∧
    ∀ f : ℝ → ℂ, IsT97J08SmoothPuncturedLoop f →
      ∃! n : ℤ, IsT97J08WindingNumber f n ∧
        (n : ℝ) = t97J08BetaIntegral f := by
  sorry
