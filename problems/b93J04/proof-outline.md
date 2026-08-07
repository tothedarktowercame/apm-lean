# Proof Outline: b93J04

The canonical Lean attempt is `lean/Main.lean`. Existing work verifies that
`r₂+r₃` is a root when `r₂²=2` and `r₃²=3`. Closer hop 1 additionally proves
that any automorphism group of cardinality four and exponent two has exactly
the frozen Klein-four product model.

- informal-solution: `informal-solution.md`
- harvested-filename: `apm-b93J04.md`

## Remaining boundary

- extract `√2` and `√3` witnesses from the root set of an arbitrary splitting
  field of the quartic;
- prove the four sign combinations are exactly the roots and establish the
  displayed four-element basis;
- construct the independent sign-change algebra automorphisms and prove the
  automorphism group has cardinality four and exponent two;
- apply the compiled Klein-four helper and the finite Galois correspondence to
  classify all five intermediate fields.
