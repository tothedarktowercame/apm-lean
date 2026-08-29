# Twice-spiral based pseudopushout extraction

`PointedCoordinateBases` records the banked boundary, left-solid-torus, and
right-solid-torus coordinate data.  It does not yet record an ambient
gluing-space base point: doing so honestly requires relating that point to the
quotient image of the chosen boundary base.  The solid-torus base objects
remain distinct: the right base is
`boundaryInclusion (h boundaryBase)`.

For a `CoordinatePseudoCocone`, `leftAutomorphismHom` and
`rightAutomorphismHom` are the genuine `Functor.mapEnd` homomorphisms at
those two objects.  `boundaryToLeftAutomorphismHom` and
`boundaryToRightAutomorphismHom` restrict them along the actual coordinate
span legs.  `glueBaseIso` is the literal component of the pseudococone glue
at the boundary base object.

`boundaryRestrictions_conjugate` proves, from naturality of that component,
that the two restrictions agree after `Iso.conj`.  The theorem
`boundaryRestrictions_conjugate_hom` packages the same statement as equality
of monoid homomorphisms.  Since the target is assumed to be a groupoid, all
endomorphism monoids here are groups; no invertibility is added by hand.

The converse is not yet available in pinned Mathlib.  Reconstructing a
groupoid functor from one vertex-group homomorphism requires, for every object,
a chosen connector from the base object, plus proofs that the definition
`connector⁻¹; loop; connector` respects composition and is independent of
the connector choices.  For the span, those choices must additionally make
the overlap glue natural at every object.  No general pointed-connected-
groupoid reconstruction API supplying this data was found, so no based group
pushout or `TwiceSpiralPushout` identification is asserted.
