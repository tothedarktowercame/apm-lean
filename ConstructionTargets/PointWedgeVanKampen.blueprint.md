# Point-wedge van Kampen blueprint

This foundation follows the `t99J01` closer audit, route step 1
`threeCircles_fundamentalGroup`, and the shared point-wedge requirements in
`t01A03`, `t92J06`, `t97A01`, and `t97A03`.  It covers the passage from the
two-open fundamental-groupoid pseudopushout to a based free-product
equivalence, its two literal wedge-leg coordinates, and the specialization to
three circles.

The construction uses Mathlib's `FundamentalGroupoid`, `FundamentalGroup`,
`ContinuousMap.HomotopyEquiv`, `CategoryTheory.Equivalence`, `SingleObj`, and
`Monoid.Coprod`.  Its geometric inputs are
`GenericPointWedgeOpenCoverComparison.genericPointWedgeCoverPackage` and
`GenericPointWedgeOverlapInclusionSquares.genericPointWedgeOverlapInclusionSquares`.
Its van Kampen input is
`TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence`.
It does not use the false assertion that a `Functor.asEquivalence`
choice-selected counit component is literally the identity.

### B1. Point-wedge open-cover package

lean: `GenericPointWedgeOpenCoverComparison.genericPointWedgeCoverPackage` :
for topological spaces `X`, `Y`, basepoints `x₀`, `y₀`, open neighbourhoods
`M ⊆ Y`, `N ⊆ X` containing the basepoints, and pointed contractions of
`M` and `N`, produce the two open subsets of `Wedge x₀ y₀`, their union
equation, homotopy equivalences of the two pieces with `X` and `Y`, and an
equivalence of their intersection with `Unit`.

uses: existing point-wedge quotient and pointed-contraction modules

status: proved a542e9e21442ca62b32c7858468526423d70e5a9 (upstream declaration
predates the program; this commit records its use by the program)

The left open contains all of `X` and only `M` from `Y`; the right open
contains all of `Y` and only `N` from `X`.  The pointed contractions collapse
the extra neighbourhood on each side, and collapse both neighbourhoods in the
intersection.  The package records that the resulting equivalences send the
canonical left and right representatives to the original points.

### B2. Overlap inclusions become constant

lean: `GenericPointWedgeOverlapInclusionSquares.genericPointWedgeOverlapInclusionSquares` :
after applying the B1 equivalences, the two maps from the intersection model
`Unit` to the piece models are respectively `ContinuousMap.const Unit x₀`
and `ContinuousMap.const Unit y₀`.

uses: B1

status: proved a542e9e21442ca62b32c7858468526423d70e5a9 (upstream declaration
predates the program; this commit records its use by the program)

Evaluate the inverse intersection equivalence at `()`.  Its representative is
the wedge point.  The left equality follows from B1's left representative
formula.  For the right equality, use the quotient relation identifying the
left and right basepoint representatives, then use B1's right formula.

### B3. Target-natural point-wedge mapping equivalence

lean: `PointWedgeVanKampen.genericPointWedgeSingleObjMappingEquivalence` and
`PointWedgeVanKampen.genericPointWedgeSingleObjPostcomposeIso`, with the full
shared context
`{X Y} [TopologicalSpace X] [TopologicalSpace Y]
[PathConnectedSpace X] [PathConnectedSpace Y]
(x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
(hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
(cM : PointedContraction M ⟨y₀, hy⟩)
(cN : PointedContraction N ⟨x₀, hx⟩)`.
For every `(C) [Category C]`, the first declaration has type
`(FundamentalGroupoid (Wedge x₀ y₀) ⥤ C) ≌
 (SingleObj (Monoid.Coprod (FundamentalGroup X x₀)
   (FundamentalGroup Y y₀)) ⥤ C)`.
For `{C D} [Category C] [Category D] (K : C ⥤ D)`, the second declaration is
the natural isomorphism between postcomposing by `K` before and after the
first equivalence, in the same orientation as
`TwoOpenFreeProductMapping.postcomposeIso`.

uses: B1, B2,
`twoOpenFundamentalGroupoidPseudopushoutEquivalence`,
`pseudopushoutPostcomposeNatIso`,
`TwoOpenFreeProductMapping.pseudoSpanEquivalence`,
`GenericSpanPseudoCoconeTransport.pseudoCoconeEquivalenceOfSpanEquivalences`
and `GenericSpanPseudoCoconeTransport.equivalenceFunctorPostcomposeIso`,
`TwoOpenPointSpanComparison.comparison` and
`TwoOpenPointSpanComparison.postcomposeIso`,
`FreeProductPointSpanRepresentations.freeProductPointSpanEquivalence` and
`FreeProductPointSpanRepresentations.equivalenceFunctorPostcomposeIso`, and
`FreeProductRepresentationSingleObjEquivalence.representationSingleObjEquivalence`
with `FreeProductRepresentationSingleObjEquivalence.representationToFunctorPostcomposeIso`.
The pseudo-cocone/pseudo-span conversion is definitionally natural under
`GenericSpanPseudoCoconeTransport.postcomposeFunctor`.

status: proved

Apply two-open groupoid van Kampen to the B1 cover.  Transport its left,
right, and overlap functor categories along the fundamental-groupoid
equivalences induced by B1.  B2 identifies both transported overlap functors
with the constant functors at `x₀` and `y₀`.  Since `Unit` has trivial
fundamental groupoid, pseudococones over that span are exactly
representations of the coproduct of the two endomorphism groups.  Compose
with the representation/single-object equivalence.  At every stage prove a
postcomposition natural isomorphism; this is the hypothesis needed for B4.
No component of an arbitrary equivalence's unit or counit is simplified to an
identity.

### B4. Reconstruct the source groupoid equivalence

lean: `PointWedgeVanKampen.genericPointWedgeSourceEquivalence`, with
`{X Y} [TopologicalSpace X] [TopologicalSpace Y]
[PathConnectedSpace X] [PathConnectedSpace Y]
(x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
(hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
(cM : PointedContraction M ⟨y₀, hy⟩)
(cN : PointedContraction N ⟨x₀, hx⟩)` :
`FundamentalGroupoid (Wedge x₀ y₀) ≌
 SingleObj (Monoid.Coprod (FundamentalGroup X x₀)
   (FundamentalGroup Y y₀))`.

uses: B3,
`GenericTargetNaturalSourceReconstruction.sourceEquivalence`

status: planned

Instantiate target-natural source reconstruction with the family and
postcomposition isomorphisms from B3.  Its forward functor is obtained by
applying the inverse mapping-category equivalence to the identity functor;
the two round trips follow from target naturality and full faithfulness.

### B5. Extract the based fundamental-group equivalence

lean: `PointWedgeVanKampen.fundamentalGroupMulEquivOfSingleObjEquivalence` :
for `E : FundamentalGroupoid X ≌ SingleObj G`,
`FundamentalGroup X x ≃* G`.

uses: Mathlib `FullyFaithful.mulEquivEnd`, `Iso.conj`, `SingleObj.toEnd`

status: proved 72d1fcaf0745652ecbc75095af242ae860341027

Use full faithfulness to identify the endomorphisms of `mk x` with those of
its image.  The object type of `SingleObj G` is subsingleton, so conjugate
along the unique object equality and then apply `SingleObj.toEnd` in the
orientation from endomorphisms to `G`.

### B6. Literal left and right leg coordinates

lean: `PointWedgeVanKampen.genericPointWedgeLegCoordinates_vanKampen`, with
`{X Y} [TopologicalSpace X] [TopologicalSpace Y]
[PathConnectedSpace X] [PathConnectedSpace Y]
(x₀ : X) (y₀ : Y) (M : Set Y) (N : Set X)
(hM : IsOpen M) (hN : IsOpen N) (hy : y₀ ∈ M) (hx : x₀ ∈ N)
(cM : PointedContraction M ⟨y₀, hy⟩)
(cN : PointedContraction N ⟨x₀, hx⟩)` : the conjunction consisting of

1. `e (FundamentalGroup.map (includeLeft x₀ y₀) x₀ g) =
   Monoid.Coprod.inl g` for every `g : FundamentalGroup X x₀`; and
2. `e (FundamentalGroup.mapOfEq
   ⟨fun y => quotientMap x₀ y₀ (.inr y),
     (continuous_quotientMap x₀ y₀).comp continuous_inr⟩
   (Quotient.sound (Relation.EqvGen.rel _ _ Rel.base)) g) =
   Monoid.Coprod.inr g` for every `g : FundamentalGroup Y y₀`,

where `e : FundamentalGroup (Wedge x₀ y₀)
(quotientMap x₀ y₀ (.inl x₀)) ≃*
Monoid.Coprod (FundamentalGroup X x₀) (FundamentalGroup Y y₀)` is B5 applied
to B4.  The `mapOfEq` proof explicitly changes the right basepoint image to
the chosen left representative of the wedge point.

uses: B1, B2, B3, B4, B5

status: planned

For each leg, compare postcomposition of the canonical inclusion functor with
the corresponding representation functor in B3.  Evaluate the natural
isomorphism on the identity target functor and then on endomorphisms of the
base object.  B1 supplies the exact representative equalities and B2 removes
the overlap connector.  Finish by extensionality on loops.  These equations
come from the postcomposition squares; they do not assert that a
choice-selected counit component is identity.

### B7. Coproduct of free groups

lean: `PointWedgeVanKampen.coprodFreeGroupEquivFreeGroupSum` :
`Monoid.Coprod (FreeGroup α) (FreeGroup β) ≃* FreeGroup (α ⊕ β)`; and
`PointWedgeVanKampen.coprodFreeGroupFinTwoFinOne_equiv` :
`Monoid.Coprod (FreeGroup (Fin 2)) (FreeGroup (Fin 1)) ≃*
 FreeGroup (Fin 3)`.

uses: Mathlib universal properties of `Monoid.Coprod` and `FreeGroup`

status: proved bb465e3f2c88b3e4f0a9c20ef891e5da1de81bf4

Define mutually inverse homomorphisms on generators.  Prove the first round
trip by coproduct homomorphism extensionality and free-generator
extensionality, and the second by free-generator extensionality.  Specialize
and transport generators along `finSumFinEquiv`.

### B8. Rank-one free group coordinate

lean: `PointWedgeVanKampen.multiplicativeIntEquivFreeGroupFinOne` :
`Multiplicative ℤ ≃* FreeGroup (Fin 1)`.

uses: Mathlib `FreeGroup.mulEquivIntOfUnique`

status: proved 94d19bb61b8e0629afa2c1070246515757d5f0b1

The type `Fin 1` has a `Unique` instance, so Mathlib gives
`FreeGroup (Fin 1) ≃* Multiplicative ℤ`.  Take its symmetric equivalence.
This fixes the orientation needed after applying
`CircleUniversalCover.circleFundamentalGroupMulEquivInt` in B12.

### B9. Three-circle topology

lean: `PointWedgeVanKampen.threeCircles_locPathConnected` :
`LocPathConnectedSpace ThreeCircles`; and
`PointWedgeVanKampen.threeCircles_pathConnected` :
`PathConnectedSpace ThreeCircles`.

uses: the point-wedge quotient presentation of `ThreeCircles`

status: proved a542e9e21442ca62b32c7858468526423d70e5a9

Transport the standard circle instances through the two nested point-wedge
constructions.  These instances also support the later covering restriction
route, independently of the fundamental-group calculation.

### B10. Contractible circle neighborhood

lean: `PointWedgeVanKampen.circleBaseNeighborhood` : `Set Circle`, together
with `circleBaseNeighborhood_isOpen : IsOpen circleBaseNeighborhood`,
`circleBase_mem : (1 : Circle) ∈ circleBaseNeighborhood`, and
`circleBaseNeighborhood_contraction :
PointedContraction circleBaseNeighborhood ⟨1, circleBase_mem⟩`.

uses: `PointedPuncturedCircleContraction.PuncturedCircle`,
`puncturedCirclePointedContraction`

status: proved

Take `circleBaseNeighborhood = {z : Circle | (z : ℂ) ≠ -1}`.  Its complement
is the closed singleton `{-1}`, hence it is open, and `1 ≠ -1`.  Its subtype
is definitionally `PuncturedCircle`; transport
`puncturedCirclePointedContraction` across the resulting basepoint equality.

### B11. Contractible two-circle wedge neighborhood

lean: `PointWedgeVanKampen.twoCirclesBaseNeighborhood` : `Set TwoCircles`,
together with
`twoCirclesBaseNeighborhood_isOpen : IsOpen twoCirclesBaseNeighborhood`,
`twoCirclesBase_mem : twoCirclesPoint ∈ twoCirclesBaseNeighborhood`, and
`twoCirclesBaseNeighborhood_contraction :
PointedContraction twoCirclesBaseNeighborhood
  ⟨twoCirclesPoint, twoCirclesBase_mem⟩`.

uses: B10,
`PointWedgeRestrictedOpenQuotient.restrictedOpen`,
`restrictedOpen_isOpen`, `restrictedOpenHomeomorphWedge`

status: proved

Let the neighborhood be
`restrictedOpen 1 1 circleBaseNeighborhood circleBaseNeighborhood` in
`Wedge 1 1 = TwoCircles`.  B10 and `restrictedOpen_isOpen` prove openness and
membership of the wedge point.  The homeomorphism
`restrictedOpenHomeomorphWedge` identifies its subtype with the wedge of two
copies of `circleBaseNeighborhood`.  Define a simultaneous wedge contraction
by applying B10's pointed contraction on each summand at time `t`; the two
formulas agree at the identified basepoints, so `Quotient.lift` descends the
homotopy.  Its zero, one, and fixed-basepoint laws follow from the corresponding
B10 laws.  Transport this pointed contraction back through the homeomorphism.

### B12. Fundamental group of three circles

lean: `PointWedgeVanKampen.threeCirclesFundamentalGroupEquiv` :
`FundamentalGroup ThreeCircles threeBase ≃* FreeGroup (Fin 3)`.

uses: B6, B7, B8, B9, B10, B11,
`CircleUniversalCover.circleFundamentalGroupMulEquivInt`

status: planned

View `ThreeCircles` as the point wedge of the two-circle point wedge and one
circle.  Apply B6 to the inner wedge using B10 on both circle factors.  Apply
B6 to the outer wedge using B11 for the old `TwoCircles` factor and B10 for
the new circle factor.  Replace each circle fundamental group by
`FreeGroup (Fin 1)` using the circle integer coordinate followed by B8, and
combine the first two generators as `FreeGroup (Fin 2)`.  Finally compose
with B7.  The representative formulas in B6 ensure that `threeBase` is the
basepoint expected by both applications.
