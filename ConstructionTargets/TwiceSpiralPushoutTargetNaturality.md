# Target naturality of coordinate pushout representations

`postcomposeCoordinateVertexFunctor` maps both coordinate targets, their glue
isomorphism, and both integer actions through a target-groupoid functor.  Its
boundary equation uses the explicit `Functor.map_conj` theorem, so the mapped
glue transports remain visible.

`postcompose_coordinate_pushout_action` applies
`Monoid.PushoutI.hom_ext_nonempty`.  The false generator is the mapped left
action; the true generator is closed by `map_conj` for the inverse glue.
`coordinateToPushoutPostcomposeIso` packages the resulting identity-component
natural isomorphism and proves morphism naturality.

The inverse-functor comparison and full target-change compatibility of the
category equivalence remain a separate packet.  No source-category
equivalence is inferred here.
