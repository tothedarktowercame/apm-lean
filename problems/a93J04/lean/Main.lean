import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# APM a93J04: Lp norms converge to L∞ norm

**Problem.** If f : [0,1] → ℝ is bounded Lebesgue measurable, then
‖f‖ₚ → ‖f‖∞ as p → ∞.

## Proof

**Upper bound:** |f| ≤ ‖f‖∞ a.e. ⟹ ‖f‖ₚ ≤ ‖f‖∞ · 1^{1/p} = ‖f‖∞.
**Lower bound:** For c < ‖f‖∞, the set E_c = {|f| > c} has positive measure.
‖f‖ₚ ≥ c · m(E_c)^{1/p} → c as p → ∞.
**Combine:** lim inf ≥ ‖f‖∞ ≥ lim sup.

## Statement repair note

Uses Mathlib's `eLpNorm` (with exponent `⊤` for L∞) and `Measure.restrict`
for the measure on [0,1]. The convergence is stated via `Tendsto` along
`atTop` in the real exponent, mapped to `ℝ≥0∞` via `ENNReal.ofReal`.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory ENNReal Filter Set
open scoped Topology

namespace ApmCanaries.A93J04

/-- The L∞ norm of f equals the essential supremum of ‖f‖₊. -/
lemma eLpNorm_top_eq_essSup {α : Type*} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace α] (f : α → E) (μ : Measure α) :
    eLpNorm f ⊤ μ = essSup (fun x => ‖f x‖₊ : α → ℝ≥0∞) μ := by
  rfl

/-- **Main theorem:** For bounded measurable f on [0,1], ‖f‖ₚ → ‖f‖∞.

    **SORRY BOUNDARY:** The proof combines:
    (1) Upper bound: `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` with q = ∞
        gives ‖f‖ₚ ≤ ‖f‖∞ · μ(univ)^{1/p} = ‖f‖∞ (since μ([0,1]) = 1).
    (2) Lower bound: for c < ‖f‖∞, E_c = {|f| > c} has positive measure
        (definition of essSup). Then ‖f‖ₚ ≥ c · m(E_c)^{1/p} → c.
    (3) Squeeze: lim inf ≥ ‖f‖∞ ≥ lim sup.
    The upper bound follows from Mathlib's `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`.
    The lower bound requires: defining the superlevel set, showing it has
    positive measure from the essSup definition, and proving the integral
    bound ‖f‖ₚ ≥ c · m(E_c)^{1/p} from ∫_{E_c} |f|^p ≥ c^p · m(E_c).
    The final squeeze uses `tendsto_of_le_le_of_tendsto` or similar.
    Tried: `eLpNorm_le_eLpNorm_mul_rpow_measure_univ` for the upper bound
    (works directly). For the lower bound, the key inequality is:
    `eLpNorm f p μ ≥ ENNReal.ofReal c * μ {x | c < ‖f x‖} ^ (1/p.toReal)`
    which follows from restricting the integral to E_c. -/
theorem tendsto_eLpNorm_atTop
    {α : Type*} [MeasurableSpace α] {f : α → ℝ} {μ : Measure α}
    (hf : AEStronglyMeasurable f μ)
    (hf_bdd : eLpNorm f ⊤ μ ≠ ⊤)
    (hμ_fin : μ Set.univ < ⊤) :
    Tendsto (fun p : ℝ => eLpNorm f (ENNReal.ofReal p) μ)
      atTop (𝓝 (eLpNorm f ⊤ μ)) := by
  sorry

end ApmCanaries.A93J04
