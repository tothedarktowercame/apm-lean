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

## Closer hop 2

The following prerequisites are now compiled without sorries:

- `apm_a03J04_distribution_le_div_weakL1Size` derives
  `distribution f α ≤ M / ofReal α` directly from the defining supremum.
- `apm_a03J04_restrict_level_le_min` proves the exact restricted level-set
  majorant by `min (volume E) (M / ofReal α)`.
- `apm_a03J04_lintegral_rpow_eq_level_lintegral` specializes Mathlib's
  weighted layer-cake identity to `|f|` on `volume.restrict E`.

Consequently the remaining work is only the scalar ENNReal integral of this
minimum majorant, including zero/crossover cases, followed by the final
Bochner-integrability and `toReal` conversion.

## Closer hop 3

`apm_a03J04_weakL1_rpow_setIntegral_of_measure_zero` now proves the full bridge
conclusion when `volume E = 0`, using `IntegrableOn.of_measure_zero` and
`setIntegral_measure_zero`. The bridge dispatches this case and records
`0 < (volume E).toReal` in the remaining branch. The unresolved work is thus
restricted to the positive-measure scalar crossover calculation; an attempted
separate `M = 0` route still required a countable-superlevel or equivalent
lintegral-to-a.e.-zero conversion and did not eliminate that assembly.
