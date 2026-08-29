# Connector vertex-data round trip

Extraction after connector reconstruction does not recover the original base
actions definitionally.  It conjugates them by the chosen connector at each
solid-torus base object.  Those connectors need not be identities.

`leftBaseComparisonIso` and `rightBaseComparisonIso` retain the images of
these base connectors.  `roundTripHom` obtains its intertwining equations from
connector normal-form reconstruction and its base-glue square by evaluating
the banked pseudococone reconstruction glue square at the boundary base.

`roundTripInv` derives the inverse intertwining and glue equations by
categorical cancellation.  `roundTripIso` packages the objectwise isomorphism,
and `roundTripIso_naturality` proves compatibility with arbitrary
`VertexDataHom`s.  Finally, `roundTripNatIso` gives

```text
reconstructionFunctor ⋙ extractionFunctor ≅ 𝟙 VertexData.
```

Together with the pseudococone-side comparison, this supplies the two
objectwise round trips.  A category equivalence is deliberately left for a
separate packet that packages the pseudococone-side comparison naturally.
