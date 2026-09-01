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

This target stops before the counit, categorical equivalence and triangle,
reverse or equivalence-level target naturality, concrete wedge cells,
free-product reconstruction, source reconstruction, and frozen consumers.
