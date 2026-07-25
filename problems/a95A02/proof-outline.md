# Proof Outline: a95A02

## Problem

A function f : [0,1] → ℝ is absolutely continuous. Three parts:
- (a) State the definition of "absolutely continuous".
- (b) Show that for each ε > 0 there is a δ > 0 with m*(f(E)) ≤ ε whenever m*(E) ≤ δ.
- (c) Prove that if E is Lebesgue measurable subset of [0,1], then f(E) is Lebesgue measurable.

## Formalization approach

### Part (a): Definition — COMPLETE

Uses Mathlib's `AbsolutelyContinuousOnInterval f 0 1`, with the ε-δ form
delegated to `absolutelyContinuousOnInterval_iff`.

### Part (b): Lusin's condition (N) — PARTIAL (sorry)

The informal proof routes through the FTC for AC functions:
f(x) = f(0) + ∫₀ˣ f'(t)dt, then m*(f(E)) ≤ ∫_E |f'|, then absolute
continuity of the Lebesgue integral gives δ.

**Blocker:** Mathlib has `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`
(the converse: interval integrals are AC) but NOT the forward direction
(AC ⟹ integral representation). Without this, the ε-δ condition on endpoint
differences cannot be shown to control the full oscillation of f.

### Part (c): Measurability preservation — PARTIAL (sorry, inherits from b)

The σ-compact + null decomposition of E is fully proved
(`measurable_subset_Icc_eq_sigmaCompact_union_null`).
Continuous images of compact sets are compact (`ac_image_compact_is_compact`).
The gap is part (b): without Lusin condition (N), f(N) for null N is not known
to be null (hence measurable).

## Proved lemmas (zero sorry)

- `acOnUnitInterval_iff`: Classical ε-δ form of AC (delegates to Mathlib).
- `ac_continuousOn`: AC ⟹ continuous on [0,1].
- `ac_image_compact_is_compact`: Continuous image of compact under AC f is compact.
- `compact_is_measurable`: Compact subsets of ℝ are measurable.
- `measurable_subset_Icc_eq_sigmaCompact_union_null`: σ-compact + null
  decomposition of measurable subsets of [0,1], via inner regularity of volume
  (regular Haar measure) and the Archimedean property.

## Checked Lean state

- `lake env lean problems/a95A02/lean/Main.lean`: exit 0
- Sorry count: 3 (all at the same theory boundary: FTC for AC functions)
- Classification: partial
