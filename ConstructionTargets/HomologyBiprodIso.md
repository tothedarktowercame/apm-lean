# Homology biproduct isomorphism

This minimal upstream target owns the canonical comparison

```lean
homology (K ⊞ L) ≅ homology K ⊞ homology L
```

for chain complexes of additive commutative groups. It constructs the
comparison from the additive homology functor's `mapBiprod` and exposes its
hom and inverse as the expected projection lift and inclusion descent.

Component normalization belongs to `HomologyBiprodNormalization`; production
open-cover transport belongs to `ProductionOpenCoverMayerVietoris`. There is
one isomorphism definition, owned here, and no Mayer--Vietoris conclusion.
