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
the additive homology functor through it, is now compiled. The isomorphism and
its hom/inv formulas are owned upstream by `HomologyBiprodIso`; component
formulas are owned by `HomologyBiprodNormalization`. This file retains
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

The hom and inverse components of all three production isomorphisms are now
named. After expanding them and applying biproduct extensionality, the first
literal remaining goal is the left projection

```text
rangeIso(U∩V).inv ≫ intersectionIso(U,V).hom ≫
  homologyMap (biprod.lift interLeft (-interRight)) n ≫
  homologyBiprodIso.hom ≫ biprod.fst ≫ rangeIso(U).hom
= homologyMap (actual inclusion (U∩V) → U) n.
```

The right projection is identical with `biprod.snd`, the negated right
intersection leg, and the actual inclusion into `V`. These projection goals
still require normalization of `homologyMap` through the signed
`biprod.lift` and the homology-biproduct comparison before the upstream
intersection triangles apply. The arrow equality remains unclaimed.

After the upstream import-cycle repair, this target now imports
`HomologyBiprodNormalization`. Its signed-lift theorem applies once the
projection is adjacent to `homologyBiprodIso.hom`, but the first requested
conjugation still stops at the literal left component

```text
homologyMap (biprod.lift interLeft (-interRight)) n ≫
  (homologyBiprodIso.hom ≫ biprod.map rangeU rangeV) ≫ biprod.fst.
```

The newer
`homologyMap_signedLift_biprodIso_map_fst`/`map_snd` declarations state the
desired four-factor suffix, but `rw` still reports no occurrence in this
elaborated expression: the leading composite intersection transport and the
parenthesized middle production isomorphism remain part of one dependent
composition. The right component has the same residual with `biprod.snd`.
This round therefore claims neither an intersection-arrow equality, a
reassembly-arrow equality, nor production exactness.

The subsequent whiskered normalization declarations remove the missing
prefix from the statement, but the production goal elaborates as the fully
left-associated composite

```text
((((rangeInter.inv ≫ intersection.hom) ≫ homologyMap signedLift) ≫
    homologyBiprodIso.hom) ≫ biprod.map rangeU rangeV) ≫ biprod.fst,
```

whereas `whiskerLeft_homologyMap_signedLift_biprodIso_map_fst` groups the
final production-isomorphism/projection suffix. Lean reports that this exact
pattern does not occur. The `snd` component fails at the identical grouping.
No arrow equality or exactness theorem is claimed from this attempt.

Using the fully left-associated normalization lemmas as whole-expression
equalities closes the first production comparison:
`booleanIntersectionArrow_eq_production` proves that the conjugated Boolean
short-complex first map is exactly `productionIntersectionArrow`.  The proof
then uses the concrete intersection-range triangles and ambient-range
homology naturality; the right component transports the minus sign explicitly.

The next literal reassembly boundary is the target object.  The Boolean short
complex ends in chains on `smallSSet U V`, whereas `coverSmallHomologyIso`
starts at `coverSmallChains (booleanCover U V)`.  Their simplicial objects are
identified by the proved proposition
`coverSmallSSet_booleanCover U V`, but they are not definitionally the same
object at this use site.  A named homology isomorphism induced by that equality,
with its hom component normalized against `reassembly_comp_ambient`, is needed
before the production reassembly arrow can be stated without concealing a
transport.  Reassembly and production exactness remain unclaimed.

The named equality-induced interfaces `booleanSmallSSetIso`,
`booleanSmallChainsIso`, and `booleanSmallHomologyIso` now compile, including
hom/inv component formulas.  Their first ambient normalization square reduces
to

```text
ssetChains.map (eqToHom coverSmallSSet_booleanCover.symm ≫
  (coverSmallSSet (booleanCover U V)).ι)
= ssetChains.map (smallSSet U V).ι.
```

Rewriting `coverSmallSSet_booleanCover` fails because the `eqToHom` proof
depends on the subcomplex occurrence being rewritten; Lean rejects the motive
as ill-typed.  The ambient-inclusion normalization, reassembly equality, and
production exactness therefore remain unclaimed.

The equality-induced comparison has now been replaced by the concrete
`Subcomplex.homOfLE` isomorphism `smallSSetIsoCoverSmall`, owned by
`BooleanTwoCoverScaffold`. Its ambient simplicial triangle is definitional,
and `booleanSmallChainsIso_hom_comp_ambient` lifts that triangle functorially
to chains. The earlier dependent `eqToHom` obstruction is therefore removed.

The first remaining reassembly comparison is memberwise: the stored
`leftRange U` and `rightRange V` inclusions into `smallSSet U V` must be
identified, through `smallSSetIsoCoverSmall`, with
`coverMemberRangeInclusion (booleanCover U V) true` and `false`. Those two
triangles have not yet been proved, so no reassembly arrow or production
exactness is claimed.

The two stored/generic member triangles now compile upstream. This target
also defines `productionReassemblyArrow` and the open-cover union comparison
`booleanUnionProductionHomologyIso`. The first remaining literal theorem is
the full conjugation

```text
booleanPiecesProductionHomologyIso.inv ≫ homologyMap shortComplex.g ≫
  booleanUnionProductionHomologyIso.hom = productionReassemblyArrow.
```

Its two biproduct components still need to combine the chain-level reassembly
triangle, the new member triangles, `coverMemberRangeHomologyIso_naturality`,
and `homologyBiprodIso_inv_homologyMap_desc`. That composite is not asserted;
connecting maps and production exactness remain unclaimed.

The first componentwise attempt at the reassembly equality stops at the
literal association

```text
biprod.inl ≫
  (biprod.map rangeU.inv rangeV.inv ≫ homologyBiprodIso.inv) ≫
  homologyMap shortComplex.g ≫ booleanUnionProductionHomologyIso.hom.
```

`biprod.inl_map_assoc` expects the map outside the parenthesized composite and
does not rewrite this term; the `inr` component has the identical residual.
No reassembly equality, connecting map, or production exactness is asserted.

The banked fully-associated biproduct/descent theorem now closes that first
association step when used as a whole equality. The left component reduces to

```text
rangeU.inv ≫ homologyMap storedLeftToUnion ≫
  booleanUnionProductionHomologyIso.hom
= homologyMap (actual cover inclusion U → X).
```

The right component has the analogous expression for `V`. The remaining
literal task is to normalize this composite through the stored member
triangle, `booleanSmallChainsIso_hom_comp_ambient`, and cover-member homology
naturality. That equality, and hence connecting maps and production
exactness, remains unclaimed.

That memberwise normalization is now complete. The named theorems
`leftReassemblyComponent_eq_production` and
`rightReassemblyComponent_eq_production` pass through the concrete Boolean
small-chain isomorphism and cancel the ambient range isomorphism using
`coverMemberRangeHomologyIso_naturality`. The biproduct component laws then
give `booleanReassemblyArrow_eq_production`, identifying the conjugated
Boolean reassembly map with the actual descent of the two inclusion-induced
maps into the ambient space.

This target still does not claim the complete production long exact
Mayer--Vietoris sequence. The remaining work is to define the adjacent-degree
connecting morphism by conjugating the existing subcomplex connecting map and
to transport the separately compiled exactness results at intersection,
pieces, and union. Both production arrows are now identified; no arrow
comparison remains hidden in that transport.
