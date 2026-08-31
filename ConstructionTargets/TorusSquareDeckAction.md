# Torus square deck action

`TorusSquareDeckAction.lean` packages the four coordinatewise sign changes of
`Circle × Circle`, indexed by `ZMod 2 × ZMod 2`.

It proves that coordinatewise squaring is a covering map by applying
`ProductEvenlyCoveredTrivialization.isCoveringMap_productMap` to Mathlib's two
circle squaring covers.  It also proves the action law, continuity, invariance
of the cover, freeness, and the finite choice lemma that turns independent
equality/antipodality alternatives into a deck transformation.

The target does not assume regularity or fiber transitivity.  A consumer must
supply its honest classification of equality in a fiber and use
`exists_deckAction_eq_of_coordinate_choices`.
