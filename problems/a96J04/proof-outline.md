# Proof Outline: a96J04

## Problem

f : [0,1] → ℝ absolutely continuous and monotone increasing. E ⊂ [0,1] null ⟹ f(E) null.

## Proof

Given ε > 0, AC gives δ > 0. Cover E by countably many disjoint open intervals
with total length < δ. By monotonicity, f(E) ⊆ ∪[f(a_k), f(b_k)]. By AC on
finite partial sums, Σ(f(b_k) - f(a_k)) ≤ ε. So volume(f(E)) ≤ ε.

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Partial (1 sorry)
- **Proven lemmas**:
  - `monotone_image_interval`: monotone f maps [a,b] into [f(a), f(b)]
  - `monotone_image_Icc`: image containment under monotone maps
- **Remaining sorry**: `ac_monotone_maps_null_to_null` (main theorem)
- **Blocker**: The decomposition of an open subset of ℝ into countably many
  disjoint open intervals is not available as a packaged lemma in Mathlib.
  This is the single missing ingredient connecting the outer-regularity cover
  to the finite AC condition.

## References

- informal-solution: `informal-solution.md`
- problem TeX: `problem.tex`
