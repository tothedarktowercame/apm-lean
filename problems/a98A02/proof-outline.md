# Proof Outline: a98A02

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a98A02.md`

## Compiled progress

- `apm_a98A02_inner_products_summable` records Mathlib's packaged Bessel
  consequence for an abstract orthonormal sequence.
- `apm_a98A02_memLp_two` proves every bounded measurable `g n` belongs to
  `L²` for the restricted interval measure.
- `apm_a98A02_orthonormal_toLp` transports the raw integral identities through
  `MemLp.toLp` and establishes Mathlib's `Orthonormal ℝ` predicate.

## Remaining bridge

1. Identify the abstract `L²` inner products with the frozen raw integral
   coefficients for bounded/L² approximants.
2. Apply Bessel to those approximants.
3. Produce bounded/L² approximants of an arbitrary `L¹` function and extend
   the limit using the uniform estimate
   `|∫ (f-h)g_n| ≤ M ∫|f-h|`.
