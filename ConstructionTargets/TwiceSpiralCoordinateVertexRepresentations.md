# Integer-coordinate vertex representations

`CoordinateVertexData` records two target objects, their base glue isomorphism,
and two representations of `IntGroup`.  Its compatibility equation uses the
literal maps `leftBoundaryHom` and `rightBoundaryHom d`; conjugation by
`baseGlue` remains explicit.

`CoordinateVertexDataHom` and its category instance use left/right
intertwiners and the same oriented base-glue square as connector vertex data.

The lemmas `left_leg_coordinate` and `right_leg_coordinate` prove that the
supplied `BasedTwiceSpiralCoordinateInterface` sends the actual groupoid span
legs to the two literal integer homomorphisms.

`toCoordinateFunctor` transports source actions through `leftCoord.symm` and
`rightCoord.symm`.  `fromCoordinateFunctor` transports them back through the
forward coordinate equivalences.  Both compatibility proofs use the leg
coordinate lemmas, rather than assuming normalized span maps.

The remaining seam is packaging the two functor composites as natural
isomorphisms.  Their target objects, glue maps, and morphism components are
literal; their action fields require extensional normalization of
`MulEquiv.symm_apply_apply` / `apply_symm_apply` beneath `MonoidHom.comp`.
No group pushout or fundamental-group conclusion is asserted.
