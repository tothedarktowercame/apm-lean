# Strictification required for reverse two-open descent

An arbitrary `PseudoFunctorCocone` cannot be converted directly to a
`DescentObject`. Its glue identifies the two overlap objects by an isomorphism,
while `TwoOpenDescentDatum.obj_eq` asks for literal equalities with one common
object. Lean has no principle turning arbitrary categorical isomorphisms into
equalities of objects.

`CoordinatedPseudoFunctorCocone` records the precise strictification data:

- a common object function on the ambient space;
- equality coordinates for both piece functors;
- agreement of those coordinates with the pseudococone glue;
- the overlap morphism equation in common coordinates.

`CoordinatedPseudoFunctorCocone.toDescentObject` is the honest reverse
construction under those hypotheses. `HasStrictCommonObjectCoordinates`
isolates the first unavoidable condition missing from a general pseudococone.

Consequently there is no reverse functor from the currently defined category
of arbitrary pseudococones without a separate strictification construction
that replaces each piece functor by an isomorphic functor on chosen common
objects. The same issue prevents constructing `CompatibleNatTrans` from an
arbitrary `PseudoFunctorCoconeHom`: its common-coordinate component equation
is not typed until those equality coordinates are chosen. No equivalence or
ordinary pushout is claimed here.
