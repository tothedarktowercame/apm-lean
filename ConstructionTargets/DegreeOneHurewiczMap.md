# DegreeOneHurewiczMap

This target constructs the genuine degree-one Hurewicz homomorphism

```text
FundamentalGroup X x →* Multiplicative H₁(X; ℤ)
```

from the explicit singular path chain.  It descends through Mathlib's actual
relative-path-homotopy quotient, respects the `End` multiplication convention,
and is natural under continuous based maps.  The target also factors the map
canonically through `Abelianization (FundamentalGroup X x)` and proves its
compatibility with `fundamentalGroupAbelianizationMap`.

No injectivity, surjectivity, Hurewicz isomorphism, circle coordinate, or
twice-spiral matrix is asserted.  The remaining generic theorem is the
degree-one Hurewicz isomorphism identifying this explicit abelianized map with
integral singular H1.
