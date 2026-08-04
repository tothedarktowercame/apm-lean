# Proof Outline: a97J01

## Problem

Let f: ℝ → ℝ be Lebesgue measurable. Assume ∃ c > 0 such that for every bounded
measurable set A on which f is bounded, |∫_A f dm| ≤ c. Prove that f is integrable
(∫|f| ≤ 2c).

Note: problem.tex says "prove f is measurable" which is circular. The intended
conclusion is integrability.

## Strategy

Exhaustion + MCT: split f = f⁺ - f⁻, exhaust {f ≥ 0} by A_n = {|x|≤n, 0≤f≤n},
apply the hypothesis to each A_n, pass to the limit via MCT.

## Proved (exit 0, 0 sorries)

### Fully proved:
- A_n measurable, bounded, f bounded on A_n
- Hypothesis applied: |∫_{A_n} f| ≤ c
- On A_n, f ≥ 0: ∫_{A_n} f ≥ 0, so ∫_{A_n} f ≤ c
- B_n (negative part) fully symmetric: measurable, bounded, |∫_{B_n} f| ≤ c, ∫_{B_n} f ≥ -c

### MCT passage:
- `hlint_pos`: ∫⁻ ENNReal.ofReal(f⁺) ≤ c via MCT
- `hlint_neg`: ∫⁻ ENNReal.ofReal(f⁻) ≤ c via MCT (symmetric)
- `hlint_abs`: ∫⁻ ENNReal.ofReal|f| ≤ 2c (combination)
- Integrability conclusion from finite lintegral

The bridge is closed with `Measure.integrableOn_of_bounded`: each truncation is
contained in a finite-measure interval and f is bounded there. Then
`ofReal_integral_eq_lintegral_ofReal` converts each Bochner integral bound, and
`lintegral_iSup_ae` passes to the pointwise supremum of the truncation indicators.
The negative part is symmetric. `lintegral_add_left` combines the parts, and
`hasFiniteIntegral_iff_norm` yields integrability.

## Axioms

The main theorem uses only standard axioms: propext, Classical.choice, Quot.sound.

## Mid-solve lookups

1. psr_search "lintegral monotone convergence indicator measurable set truncate nonneg integral ENNReal"
   — no useful memories. Not used.
2. Mathlib `Integral/IntegrableOn.lean` — found and used
   `Measure.integrableOn_of_bounded`.
3. Mathlib `Integral/Lebesgue/Add.lean` — found and used `lintegral_iSup_ae`.
4. Prior solved problems a01A02 and a95A02 — confirmed usage patterns for
   `ofReal_integral_eq_lintegral_ofReal`; the conversion pattern was used.
