# Morphisms of connector-compatible vertex data

`VertexDataHom` records a left and right target morphism.  Each morphism
intertwines its vertex-group representation, and the pair satisfies the
oriented base-glue square

```text
D.baseGlue.hom ≫ right = left ≫ E.baseGlue.hom.
```

The file proves extensionality and equips fixed
`ConnectorCompatibleVertexData B C K` with a category instance.

`leftNatTrans` and `rightNatTrans` extend the two intertwiners to natural
transformations between the connector-system `constantObjectFunctor`s.  Their
naturality proofs evaluate an arbitrary groupoid arrow through its connector
normal form and then apply the corresponding intertwining equation.

`coordinatePseudoCoconeHom` uses the base-glue square verbatim for the
pseudococone glue equation.  `reconstructionFunctor` packages the resulting
one-way functor from connector-compatible vertex data to coordinate
pseudococones.

No equivalence is claimed.  Establishing one requires unit and counit
comparisons showing that extracting vertex data from an arbitrary coordinate
pseudococone and reconstructing with the fixed connectors recovers its two
piece functors and overlap glue coherently.
