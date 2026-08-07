import Mathlib

/-!
# APM a97A03

## Statement repairs

None. The conventional implicit condition `a ≤ b` in the notation `[a,b]`
is made explicit.

## Encoding questions

The interval-domain function is represented by an ambient function `ℝ → ℝ`
whose relevant behavior is restricted to `Set.Icc a b`. At the two endpoints
the derivative is encoded by `derivWithin`; this differs from the unrestricted
derivative only on a Lebesgue-null set and faithfully expresses the a.e. claim.
-/

open MeasureTheory Filter

theorem apm_a97a03 (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    (∃ B : ℝ, 0 < B ∧ ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
      |f x - f y| ≤ B * |x - y|) ↔
    (∃ C : ℝ, 0 < C ∧
      ∀ᵐ x : ℝ ∂(volume.restrict (Set.Icc a b)),
        |derivWithin f (Set.Icc a b) x| ≤ C) := by
  sorry
