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

/-- Normalization of a punctured loop lands on the unit circle. -/
lemma t97J08_norm_normalizedLoop
    {f : ℝ → ℂ} (hf : ∀ t, f t ≠ 0) (t : ℝ) :
  ‖t97J08NormalizedLoop f t‖ = 1 := by
  rw [t97J08NormalizedLoop, norm_div]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact div_self (norm_ne_zero_iff.mpr (hf t))

/-- Normalization preserves the required `2π` periodicity. -/
lemma t97J08_normalizedLoop_periodic
    {f : ℝ → ℂ} (hf : ∀ t, f (t + 2 * Real.pi) = f t) (t : ℝ) :
    t97J08NormalizedLoop f (t + 2 * Real.pi) = t97J08NormalizedLoop f t := by
  simp only [t97J08NormalizedLoop, hf]

theorem apm_t97j08 :
    IsT97J08ClosedOneFormOnPuncturedPlane t97J08Beta ∧
    ∀ f : ℝ → ℂ, IsT97J08SmoothPuncturedLoop f →
      ∃! n : ℤ, IsT97J08WindingNumber f n ∧
        (n : ℝ) = t97J08BetaIntegral f := by
  /-
  Boundary (closer hop 1): unfolding the closedness conjunct reduces it to
  differentiability of the two rational coordinate functions away from
  `z.re² + z.im² = 0`, followed by the concrete equality

  `D (x / (2π(x²+y²))) (1,0) =
     D (-y / (2π(x²+y²))) (0,1)`.

  `Complex.normSq_eq_zero` discharges the denominator side condition.  I
  tested `fun_prop` after unfolding `t97J08Beta`; it does not automatically
  propagate that nonzero denominator through these real-linear complex
  projections, and simplification does not calculate the two `fderiv`s.  A
  local closure should provide explicit `HasFDerivAt` quotient formulas and
  finish the resulting field identity.

  The winding-number conjunct is the larger boundary.  It requires lifting
  every smooth periodic normalized loop through `Real → Circle`, proving the
  endpoint displacement is a unique integer, constructing the frozen
  two-parameter periodic homotopy, and proving the beta integral equals that
  displacement by FTC.  Searches of `LEMMA-INDEX.md`, `ConstructionTargets/`,
  Mathlib's circle/covering/homotopy/integration APIs, closed winding-number
  artifacts (`a95J03`, `a96A05`, `a97J08`, `t91J03`, `t94J06`), and git
  history found no packaged circle-loop degree classification or
  degree-as-angle-integral theorem.  Those artifacts either use an opaque
  winding number, state analytic argument-principle goals, or remain blocked
  on the same topological bridge.

  CLOSER HOP 2: the two elementary normalization obligations are now compiled.
  `t97J08_norm_normalizedLoop` proves that a nowhere-zero loop normalizes to
  norm one, and `t97J08_normalizedLoop_periodic` proves normalization preserves
  the frozen `2π` periodicity. Thus the normalized map is ready to be bundled
  as a circle-valued periodic loop for a future lifting argument. A narrower
  search of `AddCircle`, `Circle.periodic_exp`, covering homotopy lifting,
  rotation/translation-number, and interval-integral periodicity sources found
  quotient maps and general lifting machinery but no theorem supplying a
  global real lift of an arbitrary circle loop or classifying its endpoint
  displacement. The translation-number API concerns monotone degree-one
  circle homeomorphisms, not arbitrary loops. Explicit experimentation on the
  first conjunct confirmed that `fun_prop` proves the two differentiability
  fields after a norm-square nonzero fact, but this snapshot has no automatic
  Fréchet quotient-derivative normalization for the final directional
  equality. The degree classification, FTC identification, and that explicit
  derivative equality remain open.
  -/
  sorry
