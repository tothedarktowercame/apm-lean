# Twice-spiral pushout representation round trips

This target completes the equivalence between integer-coordinate vertex data
and representations of the existing `TwiceSpiralPushout d`.

`recoveredPushoutAction_eq` uses `Monoid.PushoutI.hom_ext_nonempty` and the two
compiled `lift_of` generator formulas.  The pushout-side comparison therefore
has an identity target arrow.  The coordinate-side comparison has identity
left component and `baseGlue.hom` right component; the inverse uses
`baseGlue.inv`.  The intertwining equations retain the conjugation introduced
by strictification.

The objectwise comparisons are proved natural, packaged as natural
isomorphisms, and supplied with the triangle identity required by
`CategoryTheory.Equivalence.mk'`.  Composing with the banked coordinate vertex
equivalence yields
`gluingFundamentalGroupoidPushoutRepresentationEquivalence`.

This is a mapping-category equivalence.  It does not assert an isomorphism of
the ambient fundamental group; extracting that statement still requires the
pointed representability/Yoneda step.
