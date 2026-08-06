import Mathlib

/-!
# APM m99J05: A quadratic functional on a Hilbert space

## Statement repairs

None.

## Encoding questions

None. The space is an arbitrary real Hilbert space and `f` is a genuine
continuous linear functional.
-/

noncomputable section

def apm_m99J05_quadratic {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (f : V →L[ℝ] ℝ) (v : V) : ℝ :=
  (1 / 2 : ℝ) * ‖v‖ ^ 2 - f v

def apm_m99J05_isMinimizer {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (f : V →L[ℝ] ℝ) (u : V) : Prop :=
  ∀ v : V, apm_m99J05_quadratic f u ≤ apm_m99J05_quadratic f v

theorem apm_m99j05
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V →L[ℝ] ℝ) :
    (∃! u : V, apm_m99J05_isMinimizer f u) ∧
    (∀ u : V,
      apm_m99J05_isMinimizer f u ↔
        ∀ v : V, inner ℝ u v = f v) := by
  sorry
