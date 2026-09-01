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
action. This file still does not add reverse reconstruction, an equivalence,
target naturality, torus-specific connectors, or frozen-facing adapters.
