import Mathlib

/-!
# APM a03J04: Distribution functions and weak-L¹ estimates

## Statement repairs

The source calls `E` a subset of finite measure. We make explicit the standard
implicit requirement that `E` is Lebesgue measurable, so `∫_E` denotes
integration over a measurable set.

## Encoding questions

None. `ℝⁿ` is encoded as `EuclideanSpace ℝ (Fin n)`, `m` as its Lebesgue
measure, and the distribution function and weak-L¹ supremum take values in
`ℝ≥0∞` so infinite level-set measures are represented honestly.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- The ambient Euclidean space `ℝⁿ`. -/
abbrev A03J04Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The distribution function `λ(α) = m {x | |f x| > α}`. -/
def apm_a03J04_distribution {n : ℕ}
    (f : A03J04Space n → ℝ) (α : ℝ) : ℝ≥0∞ :=
  volume {x | α < |f x|}

/-- The weak-L¹ size `sup_{α > 0} α λ(α)`. -/
def apm_a03J04_weakL1Size {n : ℕ}
    (f : A03J04Space n → ℝ) : ℝ≥0∞ :=
  ⨆ α : {α : ℝ // 0 < α},
    ENNReal.ofReal α.1 * apm_a03J04_distribution f α.1

theorem apm_a03j04 (n : ℕ) :
    (∀ f : A03J04Space n → ℝ,
      Measurable f → Integrable f volume →
      (∫⁻ x, ENNReal.ofReal |f x| ∂volume) =
        ∫⁻ α in Ioi (0 : ℝ), apm_a03J04_distribution f α) ∧
    (∀ (f : A03J04Space n → ℝ) (M : ℝ≥0∞) (p : ℝ)
        (E : Set (A03J04Space n)),
      Measurable f → apm_a03J04_weakL1Size f = M → M ≠ ⊤ →
      0 < p → p < 1 → MeasurableSet E → volume E ≠ ⊤ →
      IntegrableOn (fun x => Real.rpow |f x| p) E volume) ∧
    (∀ p : ℝ, 0 < p → p < 1 →
      ∃ c : ℝ, 0 < c ∧
        ∀ (f : A03J04Space n → ℝ) (M : ℝ≥0∞)
            (E : Set (A03J04Space n)),
          Measurable f → apm_a03J04_weakL1Size f = M → M ≠ ⊤ →
          MeasurableSet E → volume E ≠ ⊤ →
          (∫ x in E, Real.rpow |f x| p ∂volume) ≤
            c * Real.rpow (volume E).toReal (1 - p) *
              Real.rpow M.toReal p) := by
  sorry
