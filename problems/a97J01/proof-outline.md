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

## Proved (exit 0, 1 sorry)

### Fully proved:
- A_n measurable, bounded, f bounded on A_n
- Hypothesis applied: |∫_{A_n} f| ≤ c
- On A_n, f ≥ 0: ∫_{A_n} f ≥ 0, so ∫_{A_n} f ≤ c
- B_n (negative part) fully symmetric: measurable, bounded, |∫_{B_n} f| ≤ c, ∫_{B_n} f ≥ -c

### Boundary (1 sorry — MCT passage):
- `hlint_pos`: ∫⁻ ENNReal.ofReal(f⁺) ≤ c via MCT
- `hlint_neg`: ∫⁻ ENNReal.ofReal(f⁻) ≤ c via MCT (symmetric)
- `hlint_abs`: ∫⁻ ENNReal.ofReal|f| ≤ 2c (combination)
- Integrability conclusion from finite lintegral

The remaining bridge: connecting the Bochner set integral ∫_{A_n} f to the
lintegral ∫⁻_{A_n} ENNReal.ofReal(f) requires `ofReal_integral_eq_lintegral_ofReal`
which needs `Integrable f (volume.restrict (A n))`. Proving integrability on each
bounded set (f bounded by n, A_n has finite measure) requires assembling Mathlib's
bounded-function-on-finite-measure integrability API.

## Axioms

The proved sub-results (within the theorem body) use only standard axioms
(propext, Classical.choice, Quot.sound). The main theorem includes sorryAx
due to the incomplete MCT passage.

## Mid-solve lookups

1. psr_search "lintegral monotone convergence indicator measurable set truncate nonneg integral ENNReal"
   — no useful memories. Not used.
