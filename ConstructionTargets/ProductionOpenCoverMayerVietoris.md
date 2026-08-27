# Production open-cover Mayer--Vietoris

This target closes the generic categorical part of transporting the existing
subcomplex Mayer--Vietoris sequence to production homology objects.

Compiled declarations:

- `transportShortComplex` and `transportShortComplexIso` conjugate both arrows
  through three supplied object isomorphisms.
- `transportShortComplex_exact` proves exactness of that presentation.
- `coverSmall_homologyMap_isIso` and `coverSmallHomologyIso` combine the
  degree-zero and positive-degree subdivision results into one all-degree
  production comparison.
- `subcomplexMayerVietoris_exact_transport` applies the transport theorem to
  the compiled exactness at the sum-of-pieces term.

The public range and memberwise cover-small naturality squares are compiled in
`SingularExcision`. This target does not replace the remaining comparison with
assumed isomorphisms or claim a production topological Mayer--Vietoris
sequence.

The middle-object isomorphism
`H_n(C(P) ⊞ C(Q)) ≅ H_n(C(P)) ⊞ H_n(C(Q))`, together with normalization of
the additive homology functor through it, is now compiled. This file retains
the conjugated-arrow exactness theorem because the final signed-arrow
equalities still contain the transports described below.

Round 4B checked the direct construction
`(HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).mapBiprod K L`.
Importing `Mathlib.Algebra.Homology.Additive`, instantiating
`preservesFiniteBiproductsOfAdditive`, and explicitly deriving
`PreservesBinaryBiproducts` from the finite instance makes it elaborate.
`homologyBiprodIso_hom` and `homologyBiprodIso_inv` expose the projection and
injection normal forms. The remaining production statement requires a single
large normalization of `IsPushout.shortComplex`'s signed maps through the
intersection equality, this biproduct isomorphism, and the cover-small
isomorphism; that equality is not asserted here.

The first concrete residual is the reassembly equation (with `P` and `Q` the
two ambient range subcomplexes):

```text
(homologyBiprodIso (ssetChains.obj P) (ssetChains.obj Q) n).inv
  ≫ homologyMap (biprod.desc (ssetChains.map (subcomplexLeftToUnion P Q))
                            (ssetChains.map (subcomplexRightToUnion P Q))) n
  ≫ (coverSmallHomologyIso cover hOpen hCover n).hom
= biprod.desc (homologyMap (actual inclusion U → U ∪ V) n)
              (homologyMap (actual inclusion V → U ∪ V) n).
```

The memberwise naturality theorem is stated before applying the biproduct
descent, while the left side above contains the `eqToIso` identifying
`P ⊔ Q` with the Boolean `coverSmallSSet`. Existing simp lemmas do not close
that transport. The analogous signed intersection equation additionally
transports `P ⊓ Q` along `ambientSubspaceRange_inf`.

The banked `ambientIntersectionRange*` coherence now supports the concrete
production objects without equality transport. This target defines
`ambientRangeProductionHomologyIso`,
`booleanIntersectionProductionHomologyIso`, and
`booleanPiecesProductionHomologyIso`, together with the actual signed
inclusion arrow `productionIntersectionArrow`.

The first remaining literal normalization is

```text
booleanIntersectionProductionHomologyIso(U,V,n).inv ≫
  homologyMap (BooleanTwoCoverScaffold.shortComplex U V).f n ≫
  booleanPiecesProductionHomologyIso(U,V,n).hom
= productionIntersectionArrow U V n.
```

All component triangles needed for this equation are compiled upstream, but
the current categorical normal form still contains the inverse of the
composite intersection isomorphism and the `biprod.mapIso`/homology-biproduct
composite. This exact arrow equality was not proved in this round, so neither
the reassembly comparison nor production Mayer--Vietoris exactness is
asserted.
