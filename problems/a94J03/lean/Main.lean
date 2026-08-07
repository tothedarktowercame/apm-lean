import Mathlib

/-!
# APM a94J03

## Statement repairs

None.

## Encoding questions

None. “Maps open sets onto open sets” is Mathlib's `IsOpenMap`, and strict
monotonicity allows either global orientation: `StrictMono f ∨ StrictAnti f`.
-/

theorem apm_a94j03 (f : ℝ → ℝ) (hf : Continuous f) (hopen : IsOpenMap f) :
    StrictMono f ∨ StrictAnti f := by
  sorry
