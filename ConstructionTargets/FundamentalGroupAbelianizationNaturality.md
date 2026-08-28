# Fundamental-group abelianization naturality

This target compiles the algebraic half of degree-one Hurewicz naturality:

- continuous maps induce maps between abelianized fundamental groups;
- those maps compose;
- the universal lift to any commutative target commutes with the induced map;
- equality of based fundamental-group maps remains equality after
  abelianization.

The pinned Mathlib and canonical ConstructionTargets contain no Hurewicz map
from loop classes to singular one-cycles and no isomorphism

```lean
Abelianization (FundamentalGroup X x) ≃ H₁(X; ℤ)
```

The first missing interface is a chain-level construction sending a path on
`Set.Icc 0 1` to the corresponding degree-one standard-simplex generator,
together with: its boundary endpoint formula, invariance modulo boundaries
under relative path homotopy, concatenation additivity modulo boundaries, and
naturality under postcomposition.  Without those results, the theorems here
cannot honestly be transported to `HomologicalComplex.homologyMap`; no such
transport or twice-spiral matrix is asserted.
