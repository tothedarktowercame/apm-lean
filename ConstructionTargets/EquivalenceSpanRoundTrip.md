# Equivalence span round-trip

`EquivalenceSpanRoundTrip.lean` proves the generic iso-valued coherence needed
when a span leg is transported through equivalences and then transported back.

The input comparison is an arbitrary natural isomorphism
`α : eO.inverse ⋙ J ⋙ eP.functor ≅ K`. The forward comparison preserves
`α.inv` together with the inverse target-piece unit. The reverse comparison
preserves `α.inv` together with the source-overlap `funInvIdAssoc`.

The four production lemmas are:

- `spanRoundTripIso_unit`
- `spanRoundTripIso_unit_inv`
- `spanRoundTripIso_counit`
- `spanRoundTripIso_counit_inv`

They cancel `α.hom` and `α.inv` honestly through naturality, whiskering,
functoriality, and the equivalence triangle identities. No functor equality is
inserted, and no `eqToIso` transport is used to replace the comparison.

The file also includes compiled residual-orientation examples showing that the
lemmas match the forward-then-reverse unit glue composite and the inverse
reverse-then-forward counit glue composite. It stops before any pseudococone
transport, reverse target naturality, concrete wedge cells, free-product work,
or frozen adapters.
