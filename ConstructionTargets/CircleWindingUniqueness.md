# Circle winding uniqueness

`IsEndpointWinding a b n` records the endpoint equation

```lean
a = b + (n : ℝ) * (2 * Real.pi).
```

The target proves that two integers satisfying this equation are equal.  It
also packages the exact reusable equivalence

```lean
Circle.exp a = Circle.exp b ↔ ∃! n : ℤ, IsEndpointWinding a b n.
```

Existence comes from `Circle.exp_eq_exp`; uniqueness uses that `2π` is
nonzero and injectivity of the integer cast into `ℝ`.

This closes the integer-uniqueness step once a circle path lift supplies real
endpoints.  It does **not** prove uniqueness of the frozen
`IsT97J08WindingNumber`, whose witnesses are two-dimensional homotopies rather
than lifts.  Connecting two such homotopies to equal endpoint displacements
still requires the absent covering-lift or circle-degree classification.  The
target therefore neither assumes nor disguises that bridge.
