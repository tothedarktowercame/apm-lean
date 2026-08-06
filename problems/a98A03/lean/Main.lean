import Mathlib

/-!
# APM a98A03

## Statement repairs

None.

## Encoding notes

The problem's functions on `[0, 1]` are represented by functions on `ℝ`, with
all hypotheses restricted to the unit interval.  Since Mathlib's integral is
the Lebesgue integral, the Riemann-integrable strengthening is expressed using
the tagged-partition definition below, including its proposed integral value.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

/-- `g` has Riemann integral `I` on `[0, 1]`, expressed by convergence of all
tagged sums as the mesh tends to zero. -/
def HasRiemannIntegralOnUnitInterval (g : ℝ → ℝ) (I : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (n : ℕ) (hn : 0 < n) (x : Fin (n + 1) → ℝ) (tag : Fin n → ℝ),
        x 0 = 0 → x (Fin.last n) = 1 → StrictMono x →
        (∀ i : Fin n, x i.castSucc ≤ tag i ∧ tag i ≤ x i.succ) →
        (∀ i : Fin n, x i.succ - x i.castSucc < δ) →
        |(∑ i, g (tag i) * (x i.succ - x i.castSucc)) - I| < ε

theorem apm_a98a03 :
    (∃ (f f' : ℝ → ℝ),
      ContinuousOn f (Icc 0 1) ∧
      (∀ᵐ x ∂volume.restrict (Icc 0 1), HasDerivAt f (f' x) x) ∧
      (∃ C : ℝ, ∀ᵐ x ∂volume.restrict (Icc 0 1), f' x ≤ C) ∧
      f 1 - f 0 ≠ ∫ x in Icc (0 : ℝ) 1, f' x ∂volume) ∧
    (∀ (f f' : ℝ → ℝ) (I : ℝ),
      ContinuousOn f (Icc 0 1) →
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x) →
      HasRiemannIntegralOnUnitInterval f' I →
      f 1 - f 0 = I) := by
  sorry
