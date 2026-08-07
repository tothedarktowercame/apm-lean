# Proof Outline: b93J04

The canonical Lean attempt is `lean/Main.lean`. Existing work verifies that
`r₂+r₃` is a root when `r₂²=2` and `r₃²=3`. Closer hop 1 additionally proves
that any automorphism group of cardinality four and exponent two has exactly
the frozen Klein-four product model.

Closer hop 2 packages the full explicit candidate root list in
`apm_b93j04_four_radical_roots`: `r₂+r₃`, `r₂-r₃`, `-r₂+r₃`, and
`-r₂-r₃` are all roots whenever the two square relations hold. This eliminates
the four repeated quartic computations from the eventual root-set argument.
Mathlib's `Polynomial.card_rootSet_eq_natDegree` can then supply exhaustion
once distinctness and separability have been proved, but it does not extract
the radicals from an abstract splitting-field instance.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b93J04.md`

## Remaining boundary

- extract `√2` and `√3` witnesses from the root set of an arbitrary splitting
  field of the quartic;
- prove the four compiled sign combinations are distinct and exhaust the root
  set, then establish the displayed four-element basis;
- construct the independent sign-change algebra automorphisms and prove the
  automorphism group has cardinality four and exponent two;
- apply the compiled Klein-four helper and the finite Galois correspondence to
  classify all five intermediate fields.
