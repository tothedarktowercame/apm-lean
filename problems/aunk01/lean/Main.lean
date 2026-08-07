import Mathlib

/-!
# APM aunk01 — translation invariance of Lebesgue measure and integration

## Statement repairs

None.

## Encoding questions

None. Borel measurability, Lebesgue measure, translation of sets, L¹
integrability, and the Lebesgue integral are represented directly.
-/

open MeasureTheory Set

noncomputable section

def apm_aunk01_translate (A : Set ℝ) (y : ℝ) : Set ℝ :=
  (fun x : ℝ ↦ x + y) '' A

theorem apm_aunk01 :
    (∀ (A : Set ℝ) (y : ℝ), MeasurableSet A →
      MeasurableSet (apm_aunk01_translate A y) ∧
      volume (apm_aunk01_translate A y) = volume A) ∧
    (∀ (f : ℝ → ℝ) (y : ℝ), Integrable f volume →
      (∫ x : ℝ, f (x + y) ∂volume) = ∫ x : ℝ, f x ∂volume) := by
  sorry
