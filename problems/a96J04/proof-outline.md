# Proof Outline: a96J04

## Problem

f : [0,1] → ℝ absolutely continuous and monotone increasing. E ⊂ [0,1] null ⟹ f(E) null.

## Proof

Given ε > 0, AC gives δ > 0. By outer regularity, place E in an open U with
volume below δ. Intersect U with (0,1), decompose it into connected components,
and identify every component C with `(sInf C, sSup C)`. Each component contains
a rational, so there are countably many; distinct components are disjoint.
For every finite component family, its total length is at most volume U, hence
below δ, and AC bounds the corresponding sum of image-interval lengths by ε.
Countable subadditivity proves the image of `E ∩ (0,1)` null. The possible
endpoint images `{f 0, f 1}` are finite and therefore null.

## Lean formalization

- **File**: `lean/Main.lean`
- **Status**: Complete (0 sorries)
- **Proven lemmas**:
  - `monotone_image_interval`: monotone f maps [a,b] into [f(a), f(b)]
  - `monotone_image_Icc`: image containment under monotone maps
- **Decomposition**: proved locally using `ConnectedComponents` of the small
  open cover. A chosen rational in each open component gives a countable
  indexing, and order-connectedness identifies each component with its open
  endpoint interval.
- **Assembly**: finite component sets are mapped injectively to endpoint pairs;
  their source-length sum is bounded by the open cover's volume, so the frozen
  finite-AC hypothesis applies without reformulation.

## References

- informal-solution: `informal-solution.md`
- problem TeX: `problem.tex`
