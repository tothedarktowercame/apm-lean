# Homology biproduct normalization

This target records the component formulas needed when a chain-level binary
biproduct is transported through the canonical additive-functor isomorphism

```lean
homology (K ⊞ L) ≅ homology K ⊞ homology L.
```

For an arbitrary lift it proves that the two projections are the homology
maps of the original components.  Specializing the right component to `-g`
gives the signed Mayer--Vietoris convention: the first projection is
`homologyMap f`, while the second is `-homologyMap g`.

In the other direction, the target proves both inclusion formulas and the
full `biprod.desc` reassembly formula after applying the inverse canonical
comparison.  These are categorical normalization statements only; no
Mayer--Vietoris exactness or geometric identification is assumed.
