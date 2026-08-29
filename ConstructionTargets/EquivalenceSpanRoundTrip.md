# Equivalence span round-trip

`EquivalenceSpanRoundTrip.lean` proves the categorical coherence needed when a
span leg is transported through equivalences and then transported back.

The forward comparison uses the inverse target-piece unit.  The reverse
comparison uses the source-overlap `funInvIdAssoc`.  The theorem
`spanRoundTrip_triangle` shows that their composite is exactly the inverse unit
of the induced functor-category equivalence, whiskered by the original leg.
`spanRoundTrip_triangle_inv` exports the inverse orientation required on the
outgoing side of a glue square.

The counit-side analogues `spanRoundTrip_counit_triangle` and
`spanRoundTrip_counit_triangle_inv` treat forward-after-reverse transport.
They retain the coordinate leg and the overlap `invFunIdAssoc`, and normalize
to the counit (respectively inverse counit) of the induced functor-category
equivalence.
The proof eliminates the supplied functor equality before simplifying its
`eqToIso`; it does not identify proof-carrying transports definitionally.

The unit orientations specialize to the twice-spiral collar legs.  The next
step is to specialize the counit orientations and paste them with coordinate
glue naturality at the overlap counit.
