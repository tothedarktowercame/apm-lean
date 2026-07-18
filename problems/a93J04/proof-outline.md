# Proof Outline: a93J04

## Problem

f : [0,1] → ℝ bounded measurable. Prove ‖f‖ₚ → ‖f‖∞ as p → ∞.

## Proof

Upper: ‖f‖ₚ ≤ ‖f‖∞ · μ^{1/p} → ‖f‖∞.
Lower: for c < ‖f‖∞, E_c = {|f|>c} has m(E_c) > 0. ‖f‖ₚ ≥ c · m(E_c)^{1/p} → c.
Squeeze: lim inf ≥ ‖f‖∞ ≥ lim sup.

## Proven zero-sorry

- `eLpNorm_top_eq_essSup`: ‖f‖∞ = essSup ‖f‖₊

## Remaining sorry (1)

`tendsto_eLpNorm_atTop`: main theorem. Requires upper bound (eLpNorm_le_eLpNorm_mul_rpow_measure_univ),
lower bound (positive measure of superlevel sets from essSup + restricting integral),
and squeeze.

## Lean state

- **Checked:** exit 0, 0 errors, 1 sorry
- **Classification:** partial
- **Validation:** `cd /home/joe/code/apm-lean && lake env lean problems/a93J04/lean/Main.lean`

## References

- Key Mathlib: `eLpNorm_le_eLpNorm_mul_rpow_measure_univ`, `essSup`, `eLpNorm`
