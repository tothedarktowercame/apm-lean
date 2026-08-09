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

The main theorem now invokes this bridge for both remaining conjuncts, so only
the bridge itself remains sorry. Mathlib's
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` supplies the weighted
layer-cake identity directly on `volume.restrict E`. The remaining proof must
bound the restricted level measure by
`min (volume E) (M / ENNReal.ofReal t)`, split at
`M.toReal / (volume E).toReal`, evaluate the two improper real-power
integrals, and convert the finite ENNReal estimate to the claimed Bochner
integrability and real bound.
