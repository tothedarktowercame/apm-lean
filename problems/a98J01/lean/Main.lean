import Mathlib

open MeasureTheory Set

noncomputable section

/-!
# APM a98J01

## Statement repairs

None.

## Encoding notes

The interval function is represented by a globally measurable real function and
then restricted to `[a,b]`. Continuity of its restriction to the large compact set
is expressed by `ContinuousOn f K`, i.e. continuity in the subspace topology on `K`.
-/

theorem apm_a98j01
    {a b : ℝ} (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : Measurable f) :
    ∀ ε : ℝ, 0 < ε →
      ∃ K : Set ℝ,
        K ⊆ Icc a b ∧
        IsCompact K ∧
        volume (Icc a b \ K) < ENNReal.ofReal ε ∧
        ContinuousOn f K := by
  sorry
