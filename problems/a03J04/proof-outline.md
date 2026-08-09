# Proof Outline: a03J04

This bundle currently has a harvested informal solution but no imported
Lean proof attempt in this problem root.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a03J04.md`

## Follow-up Needed

- extract a formalization-oriented proof outline from the informal solution
- add or select the canonical Lean attempt for this problem

## Hop 4 bridge statement

`apm_a03J04_bridge_weakL1_rpow_setIntegral` states the exact missing analytic
assembly. For `0 < p < 1`, a measurable weak-`L¹` function with finite weak
size has integrable `p`th power on every measurable finite-measure set and
satisfies

`∫_E |f|^p ≤ (1/(1-p)) · volume(E)^(1-p) · M^p`.

The proof is the layer-cake level-set split followed by
`integrableOn_Ioi_rpow`, with the required ENNReal/real conversions. The first
conclusion closes part (b); the second closes part (c) using
`c = 1 / (1-p)`.
