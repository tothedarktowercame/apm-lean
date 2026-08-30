# Twice-spiral final target naturality

`TwiceSpiralFinalTargetNaturality.lean` proves pointwise target naturality of
the complete consumer-facing equivalence for every functor `H : C ⥤ D`.

The forward square is the left-associated vertical composite of four existing
comparisons:

1. `gluingPseudopushoutPostcomposeNatIso`, wrapped as a reducible
   `CatCommSq`;
2. `actualCoordinatePseudoCoconeEquivalence_targetNaturality`;
3. `extractionPostcomposeSquare`;
4. `vertexSingleObjSquare`.

The composite's vertical equivalences reduce definitionally to
`gluingFundamentalGroupoidSingleObjMappingEquivalence`; the Lean file includes
an `rfl` check of that exact left-associated composition.  The forward
`gluingFundamentalGroupoidSingleObjMappingEquivalence_postcomposeIso` is the
square's isomorphism.  The reverse comparison is not rebuilt: its square is
the `CatCommSq.vInv` mate of the same named equivalences, and
`gluingFundamentalGroupoidSingleObjMappingEquivalence_inversePostcomposeIso`
extracts its isomorphism.

This retains all component coherence proved in the focused targets.  The
result is pointwise in an arbitrary target functor `H`.  Identity and
composition coherence between target functors has not yet been packaged, so
this file does not claim a pseudonatural equivalence.  It also does not address
representability, source equivalence, 2-Yoneda, endomorphism extraction, or the
frozen `t01J03` closure.
