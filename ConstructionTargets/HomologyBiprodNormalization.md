# Homology biproduct normalization

This target records the component formulas needed when a chain-level binary
biproduct is transported through the canonical additive-functor isomorphism

```lean
homology (K ⊞ L) ≅ homology K ⊞ homology L.
```

The isomorphism itself and its hom/inverse formulas have one upstream owner,
`HomologyBiprodIso`; this module only owns normalization through that object.

It also owns the generic preadditive sign normalization used by the component
calculations: a negated middle leg of a fully left-associated five-morphism
composite can be pulled to the outside.  A specialization with a final
biproduct second projection matches the association used by production
right-component coordinates.

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

Fully left-associated corollaries spell the same two equations exactly as a
long production composite elaborates them: the prefix, signed lift homology
map, canonical biproduct comparison, componentwise postmap, and projection
are parenthesized successively from the left.  They follow solely by category
associativity from the whiskered formulas.

Reassembly has matching fully associated component laws.  Given arbitrary
maps `u` and `v` into the two homology components, precomposing the canonical
inverse comparison and the homology map of `biprod.desc f g` by the left or
right inclusion recovers respectively `u ≫ homologyMap f` or
`v ≫ homologyMap g`.  The statements retain the nested association used by
the production composite and are derived explicitly from `biprod.inl_map_assoc`
or `biprod.inr_map_assoc` and the unwhiskered inverse-descent laws.
