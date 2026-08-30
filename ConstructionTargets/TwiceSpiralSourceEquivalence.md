# Twice-spiral source equivalence

`TwiceSpiralSourceEquivalence.lean` reconstructs the source-category
equivalence

```lean
FundamentalGroupoid (Gluing h) ≌ SingleObj (TwiceSpiralPushout d)
```

from the banked mapping-category equivalences and their pointwise target
naturality.

For the gluing-side round trip, the proof evaluates the forward
target-naturality comparison at `gluingToPushoutCandidate` with target functor
`pushoutToGluingCandidate`.  It then composes with the mapping equivalence's
counit and the left unitor.  The resulting image isomorphism is reflected by
`Functor.preimageIso`, using full faithfulness of the equivalence's forward
functor.

For the one-object-side round trip, the proof evaluates the inverse mate at
`pushoutToGluingCandidate`, composes with the mapping equivalence's unit and
the left unitor, and reflects the result through the fully faithful inverse
functor.

Finally, `CategoryTheory.Equivalence.mk` adjointifies these two round-trip
isomorphisms.  In particular, the triangle identity is supplied by the
categorical construction rather than asserted separately.

Only the target-naturality components at the two candidate functors are used.
Identity/composition coherence for a pseudonatural equivalence is unnecessary
for this source reconstruction and is not claimed.  This target also does not
extract a chosen-object endomorphism group, identify it with `ZMod 2`, edit
the frozen `t01J03` statement, or claim that problem closed.
