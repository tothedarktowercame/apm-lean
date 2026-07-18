# Proof Outline: a93A04

## Problem

f : [0,1] → ℝ is absolutely continuous iff there exist Lipschitz fₙ on [0,1]
with V(fₙ - f) → 0 (total variation convergence).

## Proof

**(⟸)** Lipschitz ⟹ AC (Mathlib). V-limit of AC ⟹ AC (ε-δ argument).
**(⟹)** f AC ⟹ f(x) = f(0) + ∫₀ˣ f'(t) dt. Truncate: gₙ = clamp(f',-n,n),
fₙ = f(0) + ∫₀ˣ gₙ. Then fₙ Lipschitz, V(fₙ-f) = ∫|gₙ-f'| → 0 by DCT.

## Proven zero-sorry

1. `lipschitz_implies_ac`: Lipschitz ⟹ AC via `LipschitzOnWith.absolutelyContinuousOnInterval`
2. `ac_iff_lipschitz_V_approx`: main equivalence combining both directions

## Remaining sorries (2)

1. `lipschitz_V_limit_implies_ac`: V-limit of Lipschitz ⟹ AC
   (connects `eVariationOn` to ε-δ definition of AC)
2. `ac_implies_lipschitz_V_approx`: AC ⟹ V-approximable by Lipschitz
   (FTC for AC, truncation, DCT)

## Lean state

- **Checked:** exit 0, 0 errors, 2 sorries
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a93A04/lean/Main.lean`

## References

- Key Mathlib: `AbsolutelyContinuousOnInterval`,
  `LipschitzOnWith.absolutelyContinuousOnInterval`,
  `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`,
  `eVariationOn`
