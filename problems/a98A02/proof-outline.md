# Proof Outline: a98A02

The Lean formalization is partial, with one theorem-level `sorry` remaining.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-a98A02.md`

## Compiled progress

- `apm_a98A02_inner_products_summable` records Mathlib's packaged Bessel
  consequence for an abstract orthonormal sequence.

## Remaining bridge

1. Bundle the bounded measurable `g n` as elements of `L²[0,1]`.
2. Transport the frozen integral identities to `Orthonormal ℝ` in the `Lp`
   quotient.
3. Apply Bessel to bounded/L² approximants of an arbitrary `L¹` function.
4. Extend the limit using the uniform estimate
   `|∫ (f-h)g_n| ≤ M ∫|f-h|`.
