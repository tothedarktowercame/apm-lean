import Mathlib

/-!
# APM a93J03

## Statement repairs

None.  The source indexing `n = 1,2,…` is represented by `n + 1` for
`n : ℕ`.

## Encoding questions

None. Lebesgue measure is `volume`, almost-everywhere quantification uses its
standard measure filter, and absolute convergence is `Summable` of the
pointwise absolute values.
-/

open MeasureTheory Filter

def apm_a93j03_exceptionalSet (f : ℕ → ℝ → ℝ) (n : ℕ) : Set ℝ :=
  {x | |f (n + 1) x| > 1 / ((n + 1 : ℕ) : ℝ) ^ 2}

theorem apm_a93j03
    (f : ℕ → ℝ → ℝ)
    (hf : ∀ n : ℕ, Measurable (f (n + 1)))
    (hμ : ∀ n : ℕ,
      volume (apm_a93j03_exceptionalSet f n) ≤
        ((2 : ENNReal) ^ (n + 1))⁻¹) :
    ∀ᵐ x : ℝ ∂volume, Summable (fun n : ℕ => |f (n + 1) x|) := by
  sorry
