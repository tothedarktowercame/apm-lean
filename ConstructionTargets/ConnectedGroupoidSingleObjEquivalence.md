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

For a functor between connected groupoids with supplied connector systems,
`inducedVertexHom` maps the source vertex group to the target vertex group by

```lean
eqToHom hbase.symm ≫ F.map f ≫ eqToHom hbase
```

The required compatibility is explicit rather than inferred:

```lean
F.mapIso (SG.connector X) =
  (eqToIso hbase).trans (SH.connector (F.obj X))
```

Under that hypothesis, `normalForm_map` proves that normal forms commute with
the induced vertex homomorphism. `normalFormComparison` has identity components
and exposes both hom and inverse component normalizations.
`connectorFunctorComparison` then composes the associators, this normal-form
comparison, the source equivalence counit, and the left unitor in the stated
orientation from connector reconstruction through `F` to the induced
single-object functor.

This is generic and conditional on a supplied compatibility proof. It does not
construct connector systems, promote the fixture's torus/circle cells, perform
coordinate specialization or span transport, compose free products, or add
frozen uptake.
