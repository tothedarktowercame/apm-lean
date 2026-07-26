# Proof Outline: a96A01

## Problem

f ∈ L¹([0,1]), 0 < p ≤ 1, ‖f‖_p = (∫|f|^p)^{1/p}.
(a) ‖f‖_p ≤ ‖f‖_q for 0 < p < q ≤ 1; L = lim_{p→0} ‖f‖_p exists.
(b) L > 0 ⟹ |f| > 0 a.e.
(c) L ≥ exp(∫ log|f|).

## Proved lemma

- `rpow_le_one_add`: t^p ≤ 1+t for t ≥ 0, 0 < p ≤ 1 (the hint from TeX).
  Case split: t ≤ 1 → t^p ≤ 1; t > 1 → t^p ≤ t.

## Theory boundaries (4 sorries)

1. `quasiNorm_antitone` (part a): Hölder for 0 < p < 1.
2. `quasiNorm_tendsto_exists`: limit exists (monotone bounded).
3. `ae_pos_of_limit_pos` (part b): DCT for ∫|f|^p → m({f≠0}).
4. `limit_ge_geometric_mean` (part c): Jensen for exp.

## Checked Lean state

- `lake env lean problems/a96A01/lean/Main.lean`: exit 0
- Sorry count: 4
- Classification: partial
