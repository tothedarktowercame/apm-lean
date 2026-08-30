# Simply connected degree-one homology

This target turns the banked degree-one Hurewicz surjection into the reusable
vanishing theorem

```lean
simplyConnected_singularH1_isZero :
  IsZero (SingularHomology 1 (TopCat.of Y))
```

for every simply connected space `Y`.

The source `FundamentalGroup Y y` is a subsingleton by simple connectivity.
Surjectivity of `fundamentalGroupH1Hom y` therefore makes its multiplicative
`IntegralH1 Y` target a subsingleton.  The proof transports that fact only
across Lean's additive/multiplicative type synonym, then applies the canonical
`AddCommGrpCat.isZero_of_subsingleton`; it does not assume homology vanishing or
change coefficient categories.
