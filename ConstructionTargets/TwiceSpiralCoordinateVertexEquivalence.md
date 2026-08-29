# Connector vertex data in integer coordinates

`vertexRoundTripIso` and `coordinateRoundTripIso` use identity component arrows
because both transports preserve the target objects and base-glue isomorphism
literally.  Their intertwining proofs normalize the two composites beneath
`MonoidHom.comp` using the inverse laws for `leftCoord` and `rightCoord`.

The objectwise isomorphisms are natural, and `coordinate_vertex_triangle`
proves the remaining triangle identity componentwise.  These results package
`vertexDataCoordinateEquivalence`.

`gluingFundamentalGroupoidCoordinateVertexEquivalence` exposes
`(FundamentalGroupoid (Gluing h) ⥤ C) ≌ CoordinateVertexData C` in the supplied
integer coordinates.  It does not use `Monoid.PushoutI` and makes no based
fundamental-group identification.
