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

Two residuals remain, exactly:

1. duplicated `postcomposeRepresentationFunctor` constants;
2. the missing generic target-natural source reconstruction theorem.

This target does not claim target naturality, source reconstruction, a
fundamental-group calculation, or frozen-problem uptake.
