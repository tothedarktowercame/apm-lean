import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# APM a01A02: Weak L² bound implies L¹ bound on sets

**Problem.** Let `f : ℝⁿ → ℝ` be Lebesgue measurable with
`m{|x : |f(x)| > λ} ≤ C λ⁻²` for some constant `C > 0`. Prove that there
exists a constant `C₁` such that for any Borel set `E ⊂ ℝⁿ` with
`0 < m(E) < ∞`, we have `∫_E |f(x)| dx ≤ C₁ √(m(E))`.

**Statement repair note.**

The informal-solution file `apm-a01A02.md` was harvested with the **wrong
content**: it contains the proof for a01A01 (typewriter sequence), not a01A02
(weak-type estimate). The proposed Lean statements are for the typewriter
problem. This file implements the correct problem from `a01A02.tex`.

**Proof.**

By the layer cake formula (Cavalieri's principle):
`∫_E |f| dm = ∫_0^∞ m(E ∩ {|f| > t}) dt`.

Using `m(E ∩ {|f| > t}) ≤ min(m(E), C/t²)`, split the integral at
`t₀ = √(C/m(E))`:

- `∫_0^{t₀} m(E) dt = m(E) · t₀ = m(E) · √(C/m(E)) = √(C·m(E))`
- `∫_{t₀}^∞ C/t² dt = C/t₀ = C · √(m(E)/C) = √(C·m(E))`

Total: `2√(C·m(E))`. So `C₁ = 2√C` suffices.

**Formalization status.**

The theorem statement is correct and captures the mathematical problem
faithfully. The proof requires the layer cake formula
(`Integrable.integral_eq_integral_meas_lt`) applied to `|f|` restricted to
`E`, combined with a careful integral splitting argument. The main
formalization challenges are:
1. Establishing integrability of `|f| · 𝟙_E` (needed for the Bochner integral
   version of layer cake, or working with `∫⁻` and ENNReal).
2. Managing the ENNReal/Real conversions in the tail-measure bound.
3. Computing the split integral `∫_0^{t₀} min(m(E), C/t²) dt` with explicit
   bound `2√(C·m(E))`.
-/

set_option linter.unusedVariables false in
noncomputable section

open MeasureTheory Set Filter

open scoped ENNReal

namespace ApmCanaries.A01A02

variable {α : Type*} [MeasureSpace α]

/-- **Main theorem.** If `f` satisfies the weak-`L²` bound
    `m{|x : |f(x)| > t} ≤ C / t²` for all `t > 0`, then for every measurable
    set `E` with finite positive measure, `∫_E |f| dm ≤ C₁ √(m(E))`.

    The constant `C₁ = 2 √C` works, by the layer cake argument.

    **SORRY BOUNDARY:** The proof requires applying the layer cake formula
    (`Integrable.integral_eq_integral_meas_lt`) to `|f|` restricted to `E`,
    then splitting the resulting integral at `t₀ = √(C/m(E))` and bounding
    each piece. The main difficulties:
    (1) Establishing that `|f| · 𝟙_E` is integrable (to apply the Bochner
        layer cake) — this follows from the weak bound but requires proof.
    (2) Managing ENNReal/Real conversions in the tail-measure bound
        `m(E ∩ {|f| > t}) ≤ min(m(E), C/t²)`.
    (3) Computing `∫_0^{t₀} m(E) dt + ∫_{t₀}^∞ C/t² dt = 2√(C·m(E))`.
    Each piece is mathematically standard but requires careful formalization
    of the measure-theoretic hypotheses and the integral estimates.
-/
-- STATEMENT REPAIR 2026-07-30 (Joe-authorised). See faithfulness-ledger #4.
-- The weak-L² hypothesis was written with `.toReal` and no finiteness
-- side-condition. Mathlib defines `ENNReal.toReal ⊤ = 0`, so a function whose
-- superlevel sets have INFINITE measure satisfied it VACUOUSLY — machine-checked
-- refutation at α = ℝ, f ≡ 1, C = 1, applied to Icc 0 (C₁²+1). The informal
-- solution states the hypothesis as the MEASURE bound `m({|f| > λ}) ≤ C λ⁻²`
-- (line 15), so this is a translation defect, not a mathematical one. Restated
-- in `ENNReal`, where `⊤ ≤ ofReal (C/t²)` is false rather than vacuously true,
-- which is exactly the intended content.
theorem weakL2_implies_L1_bound
    (f : α → ℝ) (hf_meas : Measurable f) (C : ℝ) (hC : 0 < C)
    (hweak : ∀ t : ℝ, 0 < t →
      volume {x : α | t < |f x|} ≤ ENNReal.ofReal (C / t ^ 2)) :
    ∃ C₁ : ℝ, ∀ (E : Set α), MeasurableSet E →
      0 < (volume E).toReal → (volume E) < ⊤ →
      ∫ x in E, |f x| ≤ C₁ * Real.sqrt (volume E).toReal := by
  sorry

end ApmCanaries.A01A02
