# Target naturality for connector vertex coordinates

`postcomposeVertexDataFunctor` maps both target objects, the base glue, and the
two vertex-group actions through a target groupoid functor.  Its boundary
compatibility is obtained by `Functor.map_conj` applied to the original
compatibility equation.

The fixed fundamental-group coordinates live in the source and are unchanged
by target postcomposition.  Consequently `toCoordinatePostcomposeIso` has
identity components on both target objects.  The reverse comparison
`fromCoordinatePostcomposeIso` is packaged in the same way.  Their morphism
naturality is componentwise functoriality.

This establishes target-change compatibility for the
`VertexData ↔ CoordinateVertexData` layer only.  It does not infer an
equivalence between the source groupoids.

The connector/vertex extraction layer now has the corresponding compiled
square. `extractionPostcomposeIso` compares extracting after mapping a
coordinate pseudococone with mapping the extracted vertex data. Its left and
right components are identity arrows at the images of the two separately
chosen connector bases. The intertwining fields apply the target functor to
the extracted left and right actions, while the glue field explicitly keeps
`H.map (B.glueBaseIso Q).hom`.

Naturality is checked at the left and right connector-system bases for an
arbitrary coordinate-pseudococone morphism. No connector is identified with
an identity: the connector-normal-form arguments remain inside the actual
`coordinatePseudoCoconeVertexDataEquivalence`.

`extractionPostcomposeSquare` packages the forward comparison as a
`CatCommSq`. `reconstructionPostcomposeIsoViaVInv` is obtained from
`CatCommSq.vInv`, so its inverse-direction comparison uses that equivalence's
compiled unit, counit, triangle, and connector reconstruction proofs rather
than defining a separate reconstruction transformation.

This stops at the connector/vertex target-naturality square. It does not yet
compose the vertex, coordinate, and pseudopushout target-naturality layers,
claim source equivalence or 2-Yoneda, or modify the frozen target.
