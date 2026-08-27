# Homology biproduct normalization

This target records the component formulas needed when a chain-level binary
biproduct is transported through the canonical additive-functor isomorphism

```lean
homology (K ⊞ L) ≅ homology K ⊞ homology L.
```

The isomorphism itself and its hom/inverse formulas have one upstream owner,
`HomologyBiprodIso`; this module only owns normalization through that object.

For an arbitrary lift it proves that the two projections are the homology
maps of the original components.  Specializing the right component to `-g`
gives the signed Mayer--Vietoris convention: the first projection is
`homologyMap f`, while the second is `-homologyMap g`.

In the other direction, the target proves both inclusion formulas and the
full `biprod.desc` reassembly formula after applying the inverse canonical
comparison.  These are categorical normalization statements only; no
Mayer--Vietoris exactness or geometric identification is assumed.

The signed projection formulas are also stable under an arbitrary
postcomposition `biprod.map u v`: projection to the left gives
`homologyMap f ≫ u`, while projection to the right gives
`(-homologyMap g) ≫ v`.  These forms match consumers whose two homology
components are subsequently transported by separate comparison maps.

Both postcomposition formulas also have explicitly left-whiskered versions.
For any prefix `a` into the source homology object, they normalize the exact
association `a ≫ homologyMap (biprod.lift f (-g)) ≫
((homologyBiprodIso.hom ≫ biprod.map u v) ≫ fst/snd)` to the corresponding
left or signed-right component.  Their proofs use categorical reassociation
and the unwhiskered formulas, without relying on rewrite occurrence selection.
