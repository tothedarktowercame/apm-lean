# Coordinate pseudococones and connector vertex data

`extraction_reconstruction_triangle` proves the remaining triangle identity
componentwise.  Its two components cancel the images of the chosen base
connectors with their inverses; the connectors are never normalized to
identities.

`coordinatePseudoCoconeVertexDataEquivalence` packages the compiled extraction
and reconstruction functors, `reconstructionNatIso`, and `roundTripNatIso` as
an equivalence between coordinate pseudococones and `VertexData`.

`gluingFundamentalGroupoidVertexDataEquivalence` composes this with the
collared two-open fundamental-groupoid mapping-category equivalence.  The
result depends on the selected bases and leg-compatible connector systems.  It
does not identify the vertex-data category with `TwiceSpiralPushout d` and
does not assert a based group pushout.
