# Torus–circle wedge mapping equivalence

This target identifies functors out of the fundamental groupoid of the generic
torus–circle point wedge with functors out of the one-object category of
`Monoid.Coprod (Multiplicative (ℤ × ℤ)) (Multiplicative ℤ)`.

It first gives the structural equivalence between the actual-cover
`PseudoFunctorCocone` and `SpanPseudoCocone` categories, with explicit object
and morphism translations and identity unit, counit, and triangle data.  It
then composes the two-open fundamental-groupoid pseudopushout equivalence,
`actualToFreeProductEquivalence`, and `representationSingleObjEquivalence` in
that orientation.

The target-naturality construction keeps the two independently defined
postcomposition functors aligned by `postcomposeRepresentationAlignment`. Its
components have identity underlying morphisms, but their intertwining law is
stated against the shared, typed `mappedAction`; no representation action is
changed definitionally or discarded.

`pseudoSpanPostcomposeIso` records that the literal
`PseudoFunctorCocone`/`SpanPseudoCocone` conversion commutes with target
postcomposition. The full comparison is then pasted in five typed layers:

1. the open-cover pseudopushout comparison;
2. the pseudo-to-span conversion comparison;
3. the actual-span to free-product comparison;
4. the two representation-postcomposition implementations' alignment;
5. the representation-to-single-object comparison.

`genericWedgeSingleObjPostcomposeIso` is the resulting NatIso, oriented from
postcomposing a functor out of `FundamentalGroupoid GenericWedge` and then
applying the mapping equivalence, to first applying the mapping equivalence and
then postcomposing the resulting functor out of `SingleObj FP`.

The residuals remain:

1. source reconstruction;
2. a fundamental-group calculation and frozen-problem uptake.

This target does not claim source reconstruction, a fundamental-group
calculation, or frozen-problem uptake.
