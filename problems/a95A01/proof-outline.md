# Proof Outline: a95A01

## Problem
**(a)** Lower Riemann ≤ Lebesgue ≤ upper Riemann for bounded measurable f.
**(b)** Indicator of compact positive-measure empty-interior set is not Riemann integrable.

## Lean State
- **Checked**: yes (Lean 4 v4.29.0-rc8 + Mathlib)
- **Sorry count**: 2
- **Classification**: partial
- **Proved lemmas** (zero sorry):
  - `dense_compl_of_interior_empty`: Kᶜ is dense when interior K = ∅
  - `exists_not_mem_of_dense_compl`: every interval contains a point of Kᶜ
  - `inf_indicator_eq_zero`: inf χ_K = 0 on every interval
- **Blockers**:
  - Part (a): Riemann integral machinery not in Mathlib
  - Part (b): upper Riemann integral bound from positive measure
