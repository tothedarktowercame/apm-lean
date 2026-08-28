# Range-subcomplex to production relative chains

For ambient subsets `U,V`, this target identifies chains on the intersection
of their singular-simplex ranges with ordinary singular chains on `U ∩ V`.
It proves that the inclusion into the right range becomes the literal
topological inclusion `(U ∩ V) → V`, descends the square through cokernels,
and composes with `NestedSubspaceIntersectionComparison` to obtain

`coker(C(range U ∩ range V) → C(range V)) ≅ C(V,{x : V | x ∈ U})`.

The pushout-derived `unionToRightRelative` is transported through this
isomorphism to `coverSmallUnionToProductionRelative`; its vanishing on the
left cover member is proved.

There is deliberately no asserted equality

`ambientSubspaceRange U ⊔ ambientSubspaceRange V = ambientSubspaceRange (U ∪ V)`.

That equality is false in general: a singular simplex can cross between the
two cover members. The exact remaining comparison is therefore the chain
equation saying that `coverSmallUnionToProductionRelative`, after the
cover-small inclusion into full singular chains on `U ∪ V`, agrees with the
actual absolute-to-relative projection (and then with the compiled excision
map). Establishing it requires the subdivision/cover-small factorization and
its compatibility with the pair projection. No such equality or excision
arrow is assumed here.
