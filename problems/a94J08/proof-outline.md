# Proof Outline: a94J08

## Problem
Prove that no entire function `f` can satisfy `|f(z)| ≥ |z|^{3/2}` for all `z ∈ ℂ`.

## Proof Strategy
Case split on `f(0) = 0`:
- **Case A** (`f(0) ≠ 0`): `1/f` is entire, bounded (via Liouville) → constant → contradiction.
- **Case B** (`f(0) = 0`): Factor `f(z) = zⁿ h(z)`, derive contradictions from order analysis.

## Lean State
- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 2
- **Classification**: partial
- **Proved lemmas** (zero sorry):
  - `inv_le_one_of_le_one`: `a⁻¹ ≤ 1` when `1 ≤ a`
  - `nonzero_of_lower_bound`: `f(z) ≠ 0` for `z ≠ 0` from `|f(z)| ≥ |z|^{3/2}`
  - `norm_inv_le_one_of_lower_bound`: `|1/f(z)| ≤ 1` for `|z| ≥ 1`
- **Blockers**:
  - Case A: boundedness of `1/f` on compact disk (needs compactness + continuity argument)
  - Case B: factorization `f(z) = zⁿ h(z)` needs analytic order theory
