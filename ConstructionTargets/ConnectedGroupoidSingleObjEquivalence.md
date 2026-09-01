# Connected groupoids as single-object vertex groups

This target packages the generic categorical prerequisite for replacing a
connected groupoid equipped with explicit connectors by the one-object category
of endomorphisms of its chosen base.

For a `ConnectorSystem S`, `normalFormFunctor S` sends every object to
`SingleObj.star (End S.base)` and sends a morphism to its connector normal form.
The existing normal-form identity and composition laws supply the functor laws.

Faithfulness is the connector normal-form cancellation theorem. Fullness is
constructive: an endomorphism `f` is lifted between objects `X` and `Y` as

```lean
(S.connector X).inv ≫ f ≫ (S.connector Y).hom
```

and the connector cancellations reduce its normal form exactly to `f`.
Because the target has one object, the functor is essentially surjective.
`connectorSingleObjEquivalence` packages these three properties as an
equivalence, and its object and map formulas are explicit simp lemmas.

This target stops before connector-functor comparisons, coordinate
specialization, span transport, free-product composition, or frozen uptake.
