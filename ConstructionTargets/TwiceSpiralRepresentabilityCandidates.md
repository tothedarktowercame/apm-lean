# Twice-spiral representability candidates

Let `G` be the fundamental groupoid of the gluing and let `S` be the
single-object category of `TwiceSpiralPushout d`.  The banked equivalence has
orientation `(G ⥤ C) ≌ (S ⥤ C)`.

This target therefore defines:

- `gluingToPushoutCandidate` as the inverse image of `𝟭 S` at target `S`;
- `pushoutToGluingCandidate` as the forward image of `𝟭 G` at target `G`.

It also proves the first required target-change theorem.  A functor `C ⥤ D`
postcomposes pushout actions by mapping their endomorphisms, and
`representationToFunctorPostcomposeIso` identifies the resulting
single-object functor with ordinary functor postcomposition.  Its components
are identity arrows and its map formula is literal `H.map (R.action g)`.

The earlier geometric layers of
`gluingFundamentalGroupoidSingleObjMappingEquivalence` still need analogous
postcomposition comparisons, followed by compatibility of their composite.
Until those are proved, the fixed-target equivalences and the two candidates
are not used to claim an equivalence of source groupoids.
