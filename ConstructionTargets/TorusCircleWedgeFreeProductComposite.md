# Torus-circle wedge free-product composite

This target composes the already-established comparisons in the following
orientation:

```text
actual wedge span
  → coordinate span
  → connector endomorphism groups
  → literal point span
  → free-product representation
```

The torus group `Multiplicative (ℤ × ℤ)` remains the first coproduct factor and
the circle group `Multiplicative ℤ` remains the second. The map from the
trivial connector group to each endpoint is identified with the literal point
leg using uniqueness of `PUnit`; no strictification or heterogeneous equality
is used.

`coordinateToFreeProductEquivalence` packages the last three stages, and
`actualToFreeProductEquivalence` prepends the actual-to-coordinate comparison.
The internal `connectorSquare`, `pointSquare`, and `freeProductSquare` retain
the target-postcomposition cells of their respective stages.
`CatCommSq.vComp'` pastes them with its associators first into
`coordinateFreeProductSquare` and then, after the actual-coordinate square,
into `actualFreeProductSquare`. The exposed isomorphisms
`coordinateToFreeProductPostcomposeIso` and
`actualToFreeProductPostcomposeIso` therefore preserve target naturality for
the complete forward composite.

This target does not construct a generic equivalence between all
`FreeProductRepresentation` objects and a functor category, reconstruct a
source space or source groupoid, specialize a frozen problem, or modify any
frozen statement.
