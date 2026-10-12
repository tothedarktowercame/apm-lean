# Point-wedge van Kampen foundation

This program constructs the fundamental-group equivalence for the concrete
three-circle point wedge without relying on the non-normalized counit of
`TwoOpenFreeProductMapping.mapping`.

Milestones:

1. Prove the generic point-wedge van Kampen equivalence with literal leg
   coordinates.
2. Identify the coproduct of free groups on `Fin 2` and `Fin 1` with the free
   group on `Fin 3`. This milestone is implemented as
   `coprodFreeGroupFinTwoFinOne_equiv`.
3. Export the path-connected and locally path-connected structures for
   `ThreeCircles`. This milestone is implemented in `PointWedgeVanKampen.lean`.
4. Compose the preceding results into `threeCirclesFundamentalGroupEquiv`.
## Current categorical bridge

`fundamentalGroupMulEquivOfSingleObjEquivalence` now packages the final
category-to-group conversion: once the generic van Kampen construction gives
an equivalence from the wedge fundamental groupoid to a one-object groupoid,
the fundamental group at the displayed wedge point is identified with that
group.  It is independent of the non-normalized composite counit component.

The rank-one coordinate is also implemented in the orientation needed by the
circle specialization:
`multiplicativeIntEquivFreeGroupFinOne : Multiplicative ℤ ≃* FreeGroup (Fin 1)`.

The concrete circle input is now implemented as well:
`circleBaseNeighborhood` removes the antipode `-1`,
`circleBaseNeighborhood_isOpen` and `circleBase_mem` supply the open pointed
neighbourhood data, and `circleBaseNeighborhood_contraction` reuses the
stereographic pointed contraction of that exact subtype.

The corresponding TwoCircles input is implemented by
`twoCirclesBaseNeighborhood`: it is the restricted open wedge of two copies
of the circle neighbourhood. `wedgePointedContraction` descends the two
simultaneous pointed contractions through the wedge quotient, and
`twoCirclesBaseNeighborhood_contraction` transports the result back through
`twoCirclesBaseNeighborhoodHomeomorph`.

The generic mapping construction now has its first target-natural transport
stage. `genericPointWedgeCoordinateSpanEquivalence` transports pseudococones
from the literal two-open-cover fundamental-groupoid span to the fixed span
`FundamentalGroupoid Unit ⇒ FundamentalGroupoid X/Y`.  The comparison
isomorphisms use the strict overlap formulas from the reviewed blueprint, and
`genericPointWedgeCoordinateSpanPostcomposeIso` proves that this transport
commutes with postcomposition in the target category.  The remaining B3 work
composes this stage with the two-open pseudopushout and the point-span
free-product representation stages.

The second target-natural transport stage is also compiled.
`genericPointWedgeCoordinatePointSpanEquivalence` uses connector normal forms
based exactly at `x₀` and `y₀` to replace the coordinate fundamental
groupoids by `SingleObj (FundamentalGroup X x₀)` and
`SingleObj (FundamentalGroup Y y₀)`.  Because the overlap group is trivial,
its two transported legs are naturally isomorphic to the literal point legs.
`genericPointWedgeCoordinatePointSpanPostcomposeIso` records target
postcomposition naturality for this stage.

B3 is complete. `genericPointWedgeSingleObjMappingEquivalence` composes the
two-open pseudopushout, pseudo-span conversion, both coordinate transports,
the point-span free-product representation, and the representation-to-single-
object equivalence. `genericPointWedgeSingleObjPostcomposeIso` composes their
comparison squares, proving naturality under target postcomposition without
using a counit-identity normalization.

B4 is implemented by `genericPointWedgeSourceEquivalence`.  It applies
`GenericTargetNaturalSourceReconstruction.sourceEquivalence` directly to the
B3 mapping equivalences and their postcomposition isomorphisms, producing the
fundamental-groupoid equivalence with the free-product one-object groupoid.

The B6 calculation now has its exact based equivalence:
`genericPointWedgeFundamentalGroupEquiv` applies B5 to B4 at the literal left
representative of the wedge point.  What remains is proving that its two leg
maps are the coproduct inclusions.

The reconstruction normalization is now explicit as well.
`genericPointWedgeSourceFunctor_eq_inverse_identity` identifies B4's forward
functor with B3's inverse image of the identity, while
`genericPointWedgeSourceCounit_naturality` records the resulting conjugacy
equation.  This uses counit naturality and does not assert that its component
is an identity; B6 must cancel that conjugation by the explicit leg data.

`genericPointWedgeSourceCounit_left` and
`genericPointWedgeSourceCounit_right` specialize that equation to the two
coproduct injections.  They fix the orientation of both remaining B6
calculations: the mapped leg action occurs before the counit component and
the literal injection occurs after it.

The two equations are also solved algebraically for the mapped actions:
`genericPointWedgeMappedLeft_eq_conj` and
`genericPointWedgeMappedRight_eq_conj` express them as conjugates of the
literal coproduct injections by the single explicit counit element.  Thus the
remaining literal-coordinate step is exactly the computation eliminating
that element from B3's concrete inverse representation.

`genericPointWedgeCounitNormalization` is the inner automorphism by that
counit element.  The left and right normalization theorems prove that it
sends both computed actions to the literal coproduct injections.  The
remaining B6 step is to install this normalization in the source equivalence
and connect those actions to the two topological inclusion maps.

The normalization is now installed.  The groupoid-level
`genericPointWedgeNormalizedSourceEquivalence` postcomposes B4 with the
induced `SingleObj` equivalence, while
`genericPointWedgeNormalizedFundamentalGroupEquiv` postcomposes the based B5
coordinate with the same inner automorphism.  The remaining B6 step is the
comparison between B3's two mapped actions and the fundamental-group maps of
the literal left and right wedge inclusions.

Those literal maps are now fixed in Lean as `genericPointWedgeLeftLegMap` and
`genericPointWedgeRightLegMap`; the latter records the symmetric quotient
equality needed to change the right wedge representative to the chosen left
basepoint.  `genericPointWedgeLegCoordinates_of_mapped` proves that the two
remaining B3-to-topology comparison equations imply both B6 coordinates.
Consequently the residual is exactly those two comparison equations, with no
further normalization or basepoint transport left implicit.

`genericPointWedgeLegCoordinates_iff_mapped` proves the converse as well:
the two literal B6 equations hold if and only if the unnormalized B5 images
of the literal legs equal B3's mapped actions.  Injectivity of the explicit
inner automorphism supplies the reverse direction.  A direct `rfl` check
confirms this is not definitional; the remaining work must expose the
comparison isomorphisms in the composed B3 transport.

The B5 extraction layer has now been eliminated from that residual.
`fundamentalGroupMulEquivOfSingleObjEquivalence_apply` proves that extraction
into a `SingleObj` group evaluates exactly as the underlying equivalence
functor on endomorphisms; its proof explicitly reduces the two `eqToIso`
morphisms to the unit of the one-object group.  The specialized
`genericPointWedgeFundamentalGroupEquiv_apply` therefore rewrites both
remaining comparisons directly to maps of the reconstructed B4 functor.

`genericPointWedgeLegCoordinates_iff_sourceFunctor` packages that rewrite at
the full B6 boundary: the literal normalized leg equations are equivalent to
the two direct B4 functor-map equations.  The remaining proof must now expose
the B3 comparison isomorphisms and evaluate the reconstructed functor on the
literal left and right legs; no based-group extraction remains in the goal.

`genericPointWedgeInverseIdentityFunctor` now names the actual inverse image
of the identity under the full B3 composite.  The map rewrite and
`genericPointWedgeLegCoordinates_iff_inverseIdentity` move the entire B6
boundary onto that object.  The residual is therefore the evaluation of this
explicit inverse composite on the two literal legs, through B3's successive
span and representation equivalences.

The last inverse stage is now computed explicitly.
`genericPointWedgeIdentityRepresentation` is the representation obtained by
applying the inverse representation/`SingleObj` equivalence to the identity,
and its action on both coproduct injections is definitionally the respective
injection.  Thus no coordinate defect occurs at B3's final representation
stage; the remaining calculation lies in the preceding point-span and open
cover inverse transports.

The inverse free-product/point-span stage is now explicit as
`genericPointWedgeIdentityPointSpan`.  Its left and right functors map their
group elements definitionally to the corresponding coproduct injections.
Thus the final two B3 inverse stages preserve both generators literally; the
remaining comparison begins with the coordinate-to-point span inverse.

That inverse is now named `genericPointWedgeIdentityCoordinateSpan`.  At the
chosen base objects, the connector normal forms reduce to identity
conjugations, so its left and right maps again evaluate to the literal
coproduct injections.  B6 therefore remains only at the earlier open-cover
and homotopy-equivalence transports.

`genericPointWedgeIdentityActualSpan` now exposes the inverse homotopy
transport over the literal cover span.  Its two map formulas are definitional:
each cover-piece morphism is first mapped by the corresponding B1 groupoid
equivalence and then evaluated by the coordinate-span object.  The remaining
B6 calculation is therefore the identification of the literal wedge legs
through the open-cover pseudopushout with these two cover-piece maps.

The final two open-cover inverse stages are now named explicitly.
`genericPointWedgeIdentityPseudoCocone` has left and right components
definitionally equal to the literal actual-span components, and
`genericPointWedgeIdentityGlobalFunctor` glues that pseudococone back to the
wedge.  Unfolding the complete B3 inverse proves that this global functor is
exactly `genericPointWedgeInverseIdentityFunctor`.  The remaining B6 step is
the restriction computation identifying its maps on the two literal wedge
legs with the corresponding pseudococone component maps.

That restriction boundary is now explicit on both pieces.
`genericPointWedgeIdentityGlobalLeftRestrictionIso` and its right analogue
are the two components of the pseudopushout equivalence's counit, and the two
`_naturality` theorems give their exact conjugacy equations on arbitrary
cover-piece morphisms.  Thus B6 is reduced to computing these counit
components at the chosen wedge-point representatives and then applying the
already-proved actual-span generator formulas.

The left restriction counit component is now proved definitionally equal to
the identity at every object, not merely at the basepoint.  Combining this
with counit naturality gives
`genericPointWedgeIdentityGlobalLeftRestriction_map`: the reconstructed
global functor restricted to the left cover maps every morphism exactly as
the actual-span left functor.  Only the right restriction remains; unlike the
left component it contains the overlap glue comparison and is not
definitionally the identity.

The right restriction is now solved without erasing that comparison.
`genericPointWedgeIdentityGlobalRightRestrictionElement` names each counit
component, and `genericPointWedgeIdentityGlobalRightRestriction_map` rewrites
every reconstructed right-piece map as the actual-span map conjugated by its
two endpoint components.  The order is the one induced by `SingleObj`
composition.  The remaining calculation is to evaluate those components at
the wedge-point representative and align the literal leg lifts.

Both cover-piece representatives of the chosen wedge point are now explicit
as `genericPointWedgeLeftBase` and `genericPointWedgeRightBase`.  The left
based restriction is literal, while the right based restriction is an inner
conjugation by the single named
`genericPointWedgeIdentityGlobalRightBaseElement`.  The remaining B6 work is
to compute that element from the overlap glue and identify the lifted
left/right fundamental-group morphisms with the literal wedge-leg maps.

The pseudococone contribution to that fixed conjugator is now isolated as
`genericPointWedgeStrictificationRightBaseElement`.  At the explicit overlap
wedge-point object, it is exactly the original pseudococone glue morphism;
the theorem keeps the direction from the strictified right restriction back
to the supplied right functor.  The residual computation is the preceding
descent-counit factor and then the two literal wedge-leg lifts.

The remaining descent-counit factor is now named and proved equal to the
identity: it is only the inverse `eqToHom` transport between objects of the
one-object target.  Consequently the full fixed right restriction element,
not just its strictification component, is exactly the overlap glue morphism.
B6 now only needs to evaluate that already-constructed glue through the span
transport and align the two literal wedge-leg lifts.

The identity pseudococone-to-span inverse is now evaluated on its glue field:
it preserves that field definitionally.  Hence the full right restriction
element is also the `genericPointWedgeIdentityActualSpan` glue component at
the explicit overlap base.  The remaining transport is precisely the inverse
of `genericPointWedgeCoordinateSpanEquivalence`, followed by the literal leg
lift identifications.

That inverse is now exposed as
`genericPointWedgeIdentityCoordinateReverseSpan`, the literal
`reverseTransportObj` built from the overlap, left, and right groupoid
equivalences and the two span comparison isomorphisms.  The actual-span object
is definitionally this reverse transport, so the full right restriction
element is its glue component at the overlap base.  Expanding that component
into its three comparison factors is the remaining coordinate calculation.

The reverse-transport glue is now expanded at that base in
`genericPointWedgeIdentityCoordinateReverseSpan_glue_app`.  In categorical
order it is the inverse left comparison, then the coordinate glue whiskered
along the overlap equivalence, then the right comparison.  The remaining B6
calculation is to evaluate these three components in the one-object target
and match the resulting cover morphisms with the literal wedge-leg lifts.

The middle component is now evaluated at the object level by
`genericPointWedgeIdentityCoordinateWhiskeredGlue_app`: it is exactly the
coordinate-span glue component at the image of the explicit overlap base
under the overlap equivalence.  The remaining calculation is that coordinate
glue and the two outer comparison components, followed by the literal lifts.

At the explicit overlap representative this transported object is now reduced
to the unique object of `FundamentalGroupoid Unit` by
`genericPointWedgeIdentityCoordinateWhiskeredGlue_app_eq_unitBase`.  Thus the
middle calculation has a fixed unit-base component; its connector expansion
and the two outer comparison components remain.

That fixed component is expanded in
`genericPointWedgeIdentityCoordinateSpan_glue_unitBase`.  It is, in order,
the inverse left connector comparison, the identity point-span glue whiskered
through the Unit equivalence, and the right connector comparison.  Evaluating
these connector components and the original two outer comparisons remains.

The central factor is now computed by
`genericPointWedgeIdentityPointSpan_whiskeredGlue_eq_one`: the identity
representation's point-span glue remains the free-product unit after
whiskering through the Unit equivalence.  Only the two connector comparisons
inside this coordinate stage and the two original outer comparisons remain.

`genericPointWedgeIdentityCoordinateSpan_glue_unitBase_eq_comparisons`
then removes that unit in the correct `SingleObj` multiplication order.  The
coordinate glue is now exactly the inverse left connector comparison followed
by the right connector comparison.  Evaluating those two components remains.

`genericPointWedgeIdentityCoordinateLeftComparison_app` expands the first of
those components without imposing a false normalization.  Its categorical
order is the inverse Unit-equivalence round-trip component followed by the
inverse left-leg comparison.  Evaluating these two explicit factors, the
right connector comparison, and the two original outer comparisons remains.

The symmetric component is now expanded by
`genericPointWedgeIdentityCoordinateRightComparison_app`.  In its actual hom
direction it is the right-leg comparison followed by the Unit-equivalence
round-trip component.  Thus all four inner connector-stage factors are
explicit; their evaluation and the two original outer comparisons remain.

`genericPointWedgeIdentityCoordinateLeftLegFactor_eq_one` evaluates the
inverse left-leg factor to the free-product unit.  This uses the concrete
subsingleton-source comparison and the identity-map law, without changing the
Unit-equivalence round-trip.  Three inner factors, the outer comparisons, and
the literal lifts remain.

`genericPointWedgeIdentityCoordinateRightLegFactor_eq_one` gives the matching
calculation for the right-leg hom factor.  Both concrete leg comparisons are
therefore units; the two Unit-equivalence round-trip components, the original
outer comparisons, and the literal lifts remain.

`genericPointWedgeIdentityCoordinateLeftRoundTrip_eq_one` evaluates the
inverse Unit-equivalence round-trip factor.  The proof uses subsingleton
elimination only in `FundamentalGroupoid Unit`, before functorial transport;
it does not normalize an arbitrary equivalence.  The forward Unit round-trip,
outer comparisons, and literal lifts remain.

`genericPointWedgeIdentityCoordinateRightRoundTrip_eq_one` supplies the
forward-oriented calculation using the particular `unitInv` component of the
Unit equivalence.  Consequently all four inner connector-stage factors are
units.  Only the two outer cover-to-coordinate comparisons and the literal
lift identifications remain before completing B6.

`genericPointWedgeIdentityOuterLeftComparison_app` now expands the inverse
outer left comparison at the explicit overlap representative.  Its order is
the inverse overlap-equivalence round-trip followed by the inverse left-span
comparison.  Evaluating these factors, the outer right comparison, and the
literal lift identifications remains before completing B6.

`genericPointWedgeIdentityOuterRightComparison_app` gives the corresponding
outer-right expansion.  In the hom direction its right-span comparison comes
first and the overlap-equivalence round-trip follows.  All four outer factors
are now explicit; their evaluation and the literal lifts remain for B6.

`genericPointWedgeIdentityOuterLeftSpanFactor_eq_map` removes both whiskering
layers from the inverse left-span factor.  The result is exactly the coordinate
representation applied to the strict left-span comparison at the transported
overlap object.  That mapped comparison, the other three outer factors, and
the literal lift identifications remain for B6.

`genericPointWedgeIdentityOuterRightSpanFactor_eq_map` removes the matching
whiskering layers on the right.  Its hom orientation becomes the coordinate
right representation applied to the inverse strict right-span comparison.
The two mapped span comparisons, two overlap round-trips, and literal lifts
remain for B6.

`genericPointWedgeIdentityOuterLeftRoundTrip_eq_map` similarly removes the
postcomposition whiskering from the inverse left overlap round-trip.  It is
now the left coordinate representation applied to the explicit inverse
`funInvIdAssoc` component.  Its evaluation, the right round-trip, both mapped
span comparisons, and the literal lifts remain for B6.

`genericPointWedgeIdentityOuterRightRoundTrip_eq_map` performs the hom-oriented
right calculation.  Both overlap round-trips are now explicit representation
maps of their `funInvIdAssoc` components.  Evaluating those two component maps,
the two span-comparison maps, and the literal lifts remains for B6.

`genericPointWedgeIdentityOuterLeftRoundTripComponent_eq_unitMap` expands the
inverse left component itself.  It is the left target functor applied to the
overlap equivalence's unit at the explicit representative, not an arbitrary
identity.  Evaluating that unit map, the right component map, the two span
maps, and the literal lifts remains for B6.

`genericPointWedgeIdentityOuterRightRoundTripComponent_eq_unitInvMap` gives
the forward right analogue: the right target functor maps the overlap
equivalence's `unitInv` component.  The exact unit and inverse-unit maps, the
two span maps, and the literal lifts remain for B6.

`genericPointWedgeIdentityOuterLeftUnit_targetMap_eq_nestedMap` exposes the
exact left unit image as the left equivalence functor applied after the
actual-left functor.  In particular it records the remaining pointed map
without asserting that the equivalence unit is an identity.  Evaluating this
nested map, the inverse-unit map, both span maps, and the literal lifts remains
for B6.

`genericPointWedgeIdentityOuterRightUnitInv_targetMap_eq_nestedMap` gives the
matching right-hand expansion: the right equivalence functor is applied to the
actual-right image of the overlap `unitInv`.  Both nested component maps, the
two span maps, and the literal lifts remain for B6.

`genericPointWedgeIdentityOuterLeftUnit_actualMap_eq_inclusionMap` unfolds the
inner left stage to the fundamental-groupoid map induced by the literal
overlap-to-left inclusion.  Evaluating that inclusion image, the right nested
map, both span maps, and the literal lifts remains for B6.

`genericPointWedgeIdentityOuterRightUnitInv_actualMap_eq_inclusionMap` unfolds
the symmetric inner right stage to the fundamental-groupoid map induced by
the literal overlap-to-right inclusion.  Evaluating both inclusion images,
the two span maps, and the literal lifts remains for B6.

`genericPointWedgeIdentityOuterLeftSpanComponent_target` identifies the
target endpoint of the left-span comparison at the transported overlap
representative with the literal object `FundamentalGroupoid.mk x₀`.  The
source endpoint and resulting endomorphism cast must still be evaluated before
the coordinate-span injection theorem applies.

`genericPointWedgeIdentityOuterRightSpanComponent_target` gives the symmetric
endpoint calculation: the right-span comparison targets the literal object
`FundamentalGroupoid.mk y₀`.  Both source endpoints and their endomorphism
casts remain before the coordinate-span injection theorems apply.

`genericPointWedgeIdentityOuterLeftSpanComponent_source_eq_nestedObj` exposes
the left-span source endpoint without collapsing it to the base object: it is
the left equivalence applied after the actual-left map to the overlap
equivalence's inverse/forward round trip.  Evaluating that round trip and its
endomorphism cast remains before the left injection theorem applies.

`genericPointWedgeIdentityOuterRightSpanComponent_source_eq_nestedObj` gives
the symmetric source endpoint: the right equivalence follows the actual-right
map after the same overlap inverse/forward object round trip.  Evaluating the
two round trips and dependent casts remains before both injection theorems
apply.

`genericPointWedgeIdentityCoordinateSpan_left_map` computes the left
coordinate functor on arbitrary endpoints as the coproduct injection of the
connector normal form.  The result is stated with `HEq`, retaining the
dependent object fields until the outer left-span component is specialized.

`genericPointWedgeIdentityCoordinateSpan_right_map` is the right-hand
counterpart: arbitrary right-coordinate morphisms are `HEq` to `Coprod.inr`
of their connector normal forms.  Both outer span components can now be
specialized without identifying their dependent source objects with a base.
