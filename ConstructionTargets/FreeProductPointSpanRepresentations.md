# Generic point-span free-product representations

This target packages the object-level algebra of a pseudococone over the
trivial point span `SingleObj PUnit ⥤ SingleObj G` and
`SingleObj PUnit ⥤ SingleObj H`. It reuses
`GenericSpanPseudoCoconeTransport.SpanPseudoCocone` rather than introducing a
second incompatible pseudococone interface.

`pointHom` and `pointLeg` give the unique point-to-monoid leg. The simp
normalizations `pointLeg_star_eq`, `mapped_pointLeg_star_eq`, and
`mappedPointLegStarIso` expose that the distinguished point object maps to the
distinguished object of `SingleObj M` by definitional equality.

`PointSpanVertexData` records the two target objects, the glue isomorphism, and
the left and right monoid actions. `vertexData` extracts this from a point-span
pseudococone, `strictRightAction` transports the right action to the chosen
left target by glue conjugation, and `freeProductAction` assembles the two
actions into a `Monoid.Coprod G H` action via `Monoid.Coprod.lift`.

`FreeProductRepresentation` and `FreeProductRepresentationHom` provide the
object and morphism categories for these free-product actions. The object-level
translation `toRepresentationObj` keeps the left action literal on `inl`
generators and the right action conjugated on `inr` generators:

```lean
(toRepresentationObj ... P).action (Monoid.Coprod.inr h) =
  P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
    P.glue.inv.app (SingleObj.star PUnit)
```

For a target functor `K : C ⥤ D`, `mappedAction` sends every endomorphism in a
free-product representation through `K`. Its multiplication proof retains the
order imposed by `End.mul_def`: `action.map_mul` exposes the reversed
categorical composite and `K.map_comp` preserves it. The unit proof similarly
uses `action.map_one` and `K.map_id`. The `apply`, `inl`, and `inr` formulas
make the resulting target action explicit. This is only the action-level
prerequisite; no postcomposition functor or target-naturality isomorphism is
introduced here.

`transportedHom` and the `eqToHom` bracket lemmas isolate endpoint transport
from categorical content. `conjugatedIntertwiner` is the generic categorical
engine for passing an intertwining equation through two isomorphisms, and
`exact_inr_intertwiner` specializes it to the conjugated right generator of a
point-span pseudococone.

The generator equations extend to arbitrary coproduct words through
`Monoid.Coprod.induction_on`. In its multiplication branch,
`freeProduct_intertwiner` explicitly reconciles monoid multiplication with
categorical composition order. `toRepresentationMap` uses the literal left
component `f.left.app (SingleObj.star G)` as its underlying morphism, and
`toRepresentationFunctor` packages this construction with definitional
identity and composition laws.

The five normalization lemmas expose the map's underlying morphism, functor
objects and maps, literal left-generator action, and conjugated right-generator
action.

The reverse reconstruction restricts a free-product action along
`Monoid.Coprod.inl` and `Monoid.Coprod.inr`, so the generator choices remain
literally `G = inl` and `H = inr`. `restrictedGlue` has identity components;
its naturality follows from both point legs sending the sole point monoid
morphism to the unit. `fromRepresentationObj`, `fromRepresentationMap`, and
`fromRepresentationFunctor` package these restrictions as a point-span
pseudococone functor.

The representation-side normalization recovers the original target and full
coproduct action, and recovers a representation morphism through its left
component. On the cocone side, the left action is literal, while the right
action is transported to the left target by the original glue:

```lean
P.glue.hom.app (SingleObj.star PUnit) ≫ P.right.map h ≫
  P.glue.inv.app (SingleObj.star PUnit)
```

Accordingly, the reconstructed cocone's glue is identity on the left target.
`coconeUnitNatIso` compares the original cocone with this reconstruction. Its
left component is identity, while its forward right component is the original
glue inverse (with explicit endpoint transports) and its inverse right
component is the original glue hom. The component naturality equations,
glue squares, and inverse laws are proved directly; no strictification or
heterogeneous-equality shortcut is used.

On the representation side, both directions of the counit have the identity
on `R.target` as their underlying morphism. Their intertwining laws use the
proved equality between the round-trip action and `R.action`. These components
form `representationCounitNatIso`; naturality reduces to the identity laws in
the representation category.

`pointSpan_triangle` is the remaining compatibility required by
`CategoryTheory.Equivalence.mk'`. It yields
`freeProductPointSpanEquivalence`, oriented from point-span pseudococones to
free-product representations. Its normalization lemmas expose the forward and
inverse functors, the identity left unit component, the glue-inverse right unit
component, the identity counit, and the exact `inl`/conjugated-`inr` action
orientation.

Forward target-postcomposition naturality reuses the generic span
`postcomposeFunctor` on point-span pseudococones and maps representation actions
and intertwiners through the target functor. The action comparison proves the
`G`/`inl` generator first and preserves the conjugated `H`/`inr` action. It
induces `toRepresentationPostcomposeIso` with orientation

```lean
postcomposePointSpanFunctor G H K ⋙ toRepresentationFunctor (C := D) G H ≅
  toRepresentationFunctor (C := C) G H ⋙ postcomposeRepresentationFunctor G H K
```

and `equivalenceFunctorPostcomposeIso` exposes the same comparison through the
equivalence's forward functor, with identity underlying components.

The reverse layer is the dependent restriction comparison. For any monoid
`M` and homomorphism `ι : M →* Monoid.Coprod G H`, `restrictionPostcomposeIso`
compares restriction of the mapped action with postcomposition of the
restricted original action, with identity components and naturality for every
`M`-morphism. `reverseLeftComparison` and `reverseRightComparison` specialize
this to the `inl` and `inr` legs, and `reversePostcomposeIsoApp` packages both
forward and inverse glue squares for the reconstructed point-span cocone.

These components assemble into `fromRepresentationPostcomposeIso` with
orientation

```lean
postcomposeRepresentationFunctor G H K ⋙ fromRepresentationFunctor G H D ≅
  fromRepresentationFunctor G H C ⋙ postcomposePointSpanFunctor G H K
```

and `equivalenceInversePostcomposeIso` exposes the same comparison through the
equivalence's inverse functor. The component normalization lemmas show that
the pointwise homs on the restricted left and right legs are identity.

This file now completes both forward and reverse arbitrary-target naturality
for the point-span/free-product equivalence, but it still adds no connectors,
torus specialization, source reconstruction, or frozen uptake.
