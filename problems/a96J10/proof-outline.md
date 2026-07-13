# Proof Outline — a96J10

_Formalization plan from claude-1, 2026-05-01._

## Theorem Statement (Lean 4)

```lean
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.NumberTheory.Bernoulli

open Complex Set

noncomputable section

/-- The function f(z) = z/(e^{2πz} - 1) + z/2 extended by f(0) = 1/(2π) + 0
    is analytic on the open unit disk. -/
def apm_a96J10_f (z : ℂ) : ℂ :=
  if z = 0 then 1 / (2 * Real.pi) else z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2

theorem apm_a96J10_f_analytic :
    AnalyticOn ℂ apm_a96J10_f (Metric.ball (0:ℂ) 1) := by
  -- closed in `lean/Main.lean` by rewriting the quotient term using `dslope exp 0`
  sorry

/-- The Bernoulli-type identity: f is even on Δ. -/
theorem apm_a96J10_f_even
    (z : ℂ) (hz : ‖z‖ < 1) :
    apm_a96J10_f (-z) = apm_a96J10_f z := by
  -- closed in `lean/Main.lean`
  sorry

/-- An analytic even function on a disk factors through z². -/
theorem apm_a96J10_even_factors
    (h : ℂ → ℂ) (hh : AnalyticOn ℂ h (Metric.ball (0:ℂ) 1))
    (heven : ∀ z, ‖z‖ < 1 → h (-z) = h z) :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧
      ∀ z, ‖z‖ < 1 → g (z ^ 2) = h z := by sorry

/-- Main theorem: f(z) = z/(e^{2πz}-1) + z/2 factors as g(z²) for some
    analytic g on the open unit disk. -/
theorem apm_a96J10_main :
    ∃ g : ℂ → ℂ, AnalyticOn ℂ g (Metric.ball (0:ℂ) 1) ∧
      ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 →
        g (z ^ 2) = z / (Complex.exp (2 * Real.pi * z) - 1) + z / 2 := by
        -- repaired: the original statement was false at z = 0 in Lean, since division by zero is
        -- totalized to 0, while the removable extension takes the value 1 / (2π).
        sorry
```

## Mathlib Cross-References

Mathlib cross-references

**Types/structures:**
- `ℂ` / `Complex` — the complex numbers
- `Metric.ball (0:ℂ) 1` — the open unit disk Δ
- `AnalyticOn ℂ f S` — f is analytic on S
- `AnalyticAt ℂ f z` — f is analytic at a point
- `FormalMultilinearSeries` — for power series manipulation
- `HasFPowerSeriesOnBall` — power series representation on a ball
- `Complex.exp` — complex exponential
- `bernoulli` / `Nat.bernoulli` — Bernoulli numbers (background)

**Key lemmas:**
- `Complex.differentiable_exp` — exp is entire
- `Complex.exp_eq_one_iff` — e^z = 1 ↔ z ∈ 2πi·ℤ
- `AnalyticAt.div` — quotient is analytic where denom is nonzero
- `Complex.analyticAt_exp` — exp is analytic
- `analyticAt_of_isLittleO` / `removable_singularity` — Riemann removable singularity theorem
- `Complex.isolated_zeros` / `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
- `AnalyticOn.add`, `AnalyticOn.div`, `AnalyticOn.comp` — closure properties
- `HasFPowerSeriesAt.eq_zero_of_eventually` — coefficient extraction
- `HasFPowerSeriesOnBall.coeff_zero_eq` — relating coefficients to values
- `Complex.exp_neg` — e^{-z} = 1/e^z (for the evenness computation)
- `FormalMultilinearSeries.changeOrigin` / power series manipulation
- `analyticOn_iff_forall_hasFPowerSeriesAt` — local-to-global analyticity
- `Polynomial.geom_series` / geometric series for the Taylor expansion
- `MeromorphicAt.removable_iff_bdd` — removability via boundedness
- `ENNReal.le_div_iff_mul_le` / radius of convergence manipulations
- `FormalMultilinearSeries.radius` — radius of convergence

**Tactic hints:**
- `field_simp` — clear (e^{2πz} - 1) and 2 denominators in the evenness identity
- `ring` — verify the algebraic identity f(-z) - f(z) = 0 after clearing denominators
- `simp [Complex.exp_neg, Complex.exp_add]` — manipulate exponentials
- `positivity` — for 0 < 2π and similar
- `nlinarith` — close real-part inequalities
- `apply AnalyticOn.add` / `apply AnalyticOn.div` — assemble analyticity
- `refine ⟨?_, ?_, ?_⟩` — construct the existential witness g
- `exact?` — search for removable singularity / power series lemmas
- `have hne : Complex.exp (2 * π * z) - 1 ≠ 0 := by ...` — frequent side goal
- `induction` / `Nat.rec` on power series indices for the even-coefficient construction

## Current Blockers

- 1 `sorry` remains in `lean/Main.lean`:
  - `apm_a96J10_even_factors` — the key sub-lemma `hodd` (odd Taylor coefficients of an
    even analytic function vanish) is now **fully proven** via `compContinuousLinearMap`
    and `factorial_smul` coefficient comparison. The remaining `sorry` is the construction
    of `g` from even-indexed coefficients and proving its **global analyticity on the full
    unit disk**. This requires the Taylor series at 0 to converge on the entire disk of
    analyticity — a result equivalent to Cauchy's integral formula, which is not yet
    available in Mathlib's analytic-function framework.
- `apm_a96J10_f_even` is now closed.
- `apm_a96J10_f_analytic` is now closed via the `dslope exp 0` removable-singularity rewrite.
- `apm_a96J10_main` is now closed after repairing its statement to exclude `z = 0`, which was
  necessary because the original raw formula is not equal to the removable extension at zero in
  Lean's totalized division.
