# Periodic circle homotopy winding

This target proves the covering-space invariant needed for the remaining
`t97J08` winding classification.  A free homotopy of loops may move its
basepoint, so relative-endpoint path lifting is not directly applicable.
Instead it:

1. lifts the homotopy's left edge through `Circle.exp`;
2. uses `IsCoveringMap.liftHomotopy` to lift the entire square;
3. forms the difference between the lifted right and left endpoints; and
4. uses `IsCoveringMap.const_of_comp` to show that difference is constant,
   since its circle exponential is one for every loop slice.

`endpointWinding_transport` and `uniqueEndpointWinding_agrees` then connect
this continuous result to the integral endpoint relation from
`CircleWindingUniqueness`.  `existsUnique_endpointWinding_at` supplies the
unique integer for every loop slice directly from its lifted endpoints.

This is the exact homotopy-invariance part of frozen
`apm_t97J08_bridge_unique_windingNumber`.  The frozen predicate is stated for
a continuous `H : ℝ → ℝ → ℂ`, periodic in its first coordinate, whereas
the covering API uses a compact square `I × I` with values in the subtype
`Circle`.  The remaining construction is the explicit restriction/rescaling
adapter from `[0, 2π] × [0,1]` into `I × I`, together with the converse
existence homotopy obtained from the lifted normalized loop.  No winding
classification or beta-integral equality is assumed here.
