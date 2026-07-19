# Proof Outline: a94J07

## Problem
Show `f(z) = e^z + 8z + z³` is injective on the unit disk. Hint: Rouché's theorem.

## Proof Strategy
Two applications of Rouché's theorem (not in Mathlib):
1. `f'(z) = e^z + 8 + 3z²` has no zeros since `|e^z + 3z²| ≤ e + 3 < 8`.
2. `f` and `8z` have the same winding number (= 1) since `|e^z + z³| < |8z|`.

## Lean State
- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 4
- **Classification**: partial
- **Proved**: `norm_exp_le_e`: `|e^z| ≤ e` on `|z| ≤ 1` (zero sorry)
- **Blockers**: Rouché's theorem, winding number/argument principle (not in Mathlib)
