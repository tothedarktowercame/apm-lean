# Generic span pseudococone transport

This target defines pseudococones over an arbitrary categorical span and
transports them through equivalences of the overlap and both piece categories.
The span comparisons are arbitrary natural isomorphisms; no equality or
strictification premise replaces them.

The forward API consists of `transportObj`, `transportMap`, and
`transportFunctor`, together with `transportPostcomposeIso`, which proves that
forward transport commutes with arbitrary target postcomposition. The reverse
API consists of `reverseTransportObj`, `reverseTransportMap`, and
`reverseTransportFunctor`; both map constructions prove the full glue square.

The unit is oriented as

```lean
𝟙 (SpanPseudoCocone l r C) ≅
  transportFunctor ... ⋙ reverseTransportFunctor ...
```

`spanRoundTripIso_unit_inv_with_prefix` retains the source-overlap prefix
needed by the right side of the glue calculation. `unitGlueSquare` combines
that result with the reviewed iso-valued span round-trip cancellation and
overlap-glue naturality. `inverse_glue_square_of_forward` derives the inverse
square algebraically. The resulting `unitHom`, `unitInv`, `unitIsoApp`, and
`unitNatIso` therefore retain every comparison and endpoint transport.

The counit is oriented as

```lean
reverseTransportFunctor ... ⋙ transportFunctor ... ≅
  𝟙 (SpanPseudoCocone l' r' C)
```

The reviewed counit layer adds the left/right counit triangle and cancellation
helpers, the middle counit conjugation and whiskered reverse-glue formulas,
typed substitution lemmas, and the resulting `counitGlueSquare`, `counitHom`,
`counitInv`, `counitIsoApp`, and `counitNatIso`. It preserves arbitrary span
comparison natural isomorphisms and uses `spanRoundTripIso_counit`,
`spanRoundTripIso_counit_inv`, glue naturality at `eK.counit`, and
`inverse_glue_square_of_forward`.

The reviewed final layer adds `mapped_unit_comp_counit`, proving the exact
triangle

```lean
transportFunctor.map (unitNatIso.hom.app P) ≫
  counitNatIso.hom.app (transportFunctor.obj P) = 𝟙 _
```

componentwise via the two piece functor-category equivalences, and packages the
full equivalence as `pseudoCoconeEquivalenceOfSpanEquivalences` using
`CategoryTheory.Equivalence.mk'`. The normalization lemmas
`equivalence_functor`, `equivalence_inverse`,
`equivalence_unitIso_hom_app`, and `equivalence_counitIso_hom_app` expose the
reviewed functor, inverse, unit, and counit components by `rfl`.

This file now completes the generic span-pseudococone equivalence, but still
stops before reverse or equivalence-level target naturality, concrete wedge
cells, free-product reconstruction, source reconstruction, and frozen
consumers.
