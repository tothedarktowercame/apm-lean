# Equivalence span round-trip

`EquivalenceSpanRoundTrip.lean` proves the categorical coherence needed when a
span leg is transported through equivalences and then transported back.

The forward comparison uses the inverse target-piece unit.  The reverse
comparison uses the source-overlap `funInvIdAssoc`.  The theorem
`spanRoundTrip_triangle` shows that their composite is exactly the inverse unit
of the induced functor-category equivalence, whiskered by the original leg.
`spanRoundTrip_triangle_inv` exports the inverse orientation required on the
outgoing side of a glue square.
The proof eliminates the supplied functor equality before simplifying its
`eqToIso`; it does not identify proof-carrying transports definitionally.

Both orientations specialize to the twice-spiral collar legs.  Pasting them
with overlap-glue naturality remains downstream.
