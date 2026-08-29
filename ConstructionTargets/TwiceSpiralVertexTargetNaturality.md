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
