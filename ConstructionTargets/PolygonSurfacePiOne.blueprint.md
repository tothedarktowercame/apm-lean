# Polygon-surface fundamental-group presentation blueprint

This foundation follows the audits `t96J02` step 1
`polygonSurface_pi1_presentation`, `t97A01` steps 1--2
`polygon_openCover_retract_wedge3` and `polygon_boundaryWord_pi1`, and the
polygon-presentation uptake identified by `t92J05`, `t94J04`, and `t97A03`.
The first consumer is the concrete quotient `Surface false 2`; the shared
interfaces retain the pairing word so that the six-edge `t97A01` quotient and
the standard orientable genus-two quotient do not require a second geometric
proof.

The construction uses `Surfaces.Disk`, `Surfaces.edgePoint`, `SurfaceRel`,
`Surface`, `surfaceQuotient`, and `StatementSurfaceModels.surfacePoint`.
Its existing van Kampen input is
`TwoOpenFundamentalGroupoidPseudopushout.twoOpenFundamentalGroupoidPseudopushoutEquivalence`;
its wedge input is `PointWedgeVanKampen` (in particular the based leg
coordinates, not merely an abstract group equivalence).  It also uses
Mathlib's `IsQuotientMap`, `IsOpenMap`, `ContinuousMap.Homotopy`,
`FundamentalGroup.map`, `fundamentalGroupMulEquivOfPath`, `FreeGroup`,
`PresentedGroup`, and normal closure/quotient APIs.  No surface-classification
theorem and no CW-complex API is assumed.

## Certification of the pairing-orbit correction

Certified 2026-10-12 for implementation.  B1 makes
`PairingOrbit P.pair` the generic generator type and exposes no independent
label map.  B7 indexes wedge legs by that quotient itself; B8 is polymorphic
in its finite index type; B9 and B11 instantiate it with the same
`PairingOrbit P.pair`; and B10 does not mention generator indices.  B12 may
change indices only through the displayed standard-word equivalences, after
both inverse laws have been proved.  Consequently B7--B12 cannot identify
two distinct pairing orbits through an unconstrained label function.  This
certifies the corrected B1 and B7--B12 interfaces and authorizes B1 as the
first formalisation milestone.

The Lean file is `ConstructionTargets/PolygonSurfacePiOne.lean`.  All
quotients below carry the coinduced topology from their displayed disk map.

### B1. Finite polygon-pairing data and quotient

lean: `PolygonSurfacePiOne.PairingData`,
`PolygonSurfacePiOne.PairingOrbit`,
`PairingData.Rel`, `PairingData.Space`, `PairingData.quotientMap`, and
`PairingData.center` : a finite cyclic list of oriented boundary arcs, a
fixed-point-free involution `pair` on the arcs, and a sign on each arc.
Define `PairingOrbit pair` as the quotient of arcs by
`i ∼ j ↔ j = i ∨ j = pair i`.  This quotient type itself is the generic
generator type; `PairingData` has no separate `Label` parameter or label
field.  It also includes a proof that the endpoint relation has one
vertex class.  The quotient relation identifies paired arc parameters in the
direction prescribed by the signs.

uses: `Surfaces.Disk`, `Surfaces.edgePoint`, `Relation.EqvGen`

status: planned

Use `Fin edgeCount` for arcs and `Fin edgeCount` for polygon vertices.  Store
`pair : Equiv.Perm (Fin edgeCount)`, `pair_pair : pair (pair i) = i`,
`pair_ne : pair i ≠ i` and sign compatibility as fields rather than deriving
them later.  First prove that `j = i ∨ j = pair i` is a setoid using
`pair_pair`; only then form `PairingOrbit`.  The quotient projection supplies
every orbit, and quotient equality says exactly that two arcs belong to the
same paired pair.  There is no map capable of merging different pairs. Define
`Rel` only on boundary points and define `Space` with
`Relation.EqvGen.setoid`.  Record continuity and surjectivity of the quotient
map.  The one-vertex hypothesis is used only by B7; retaining it explicitly
prevents the false conclusion that every pairing skeleton is a wedge with
one vertex.

### B2. Standard-surface and six-edge instances

lean: `PolygonSurfacePiOne.standardPairingData (o : Bool) (g : ℕ) (hg : 0 < g)`,
`standardPairingData_space_homeomorph`, and
`torusRP2PairingData` with its quotient comparison interface.

uses: B1, `Surfaces.SurfaceRel`, `Surfaces.Surface`

status: planned

For the orientable word prove a separate
`PairingOrbit pair ≃ Fin g × Bool`; for the nonorientable word prove
`PairingOrbit pair ≃ Fin g`.  These are specialization theorems, not fields
of generic data.  For the six-edge word the analogous equivalence sends the
three arc-pair orbits to `a`, `b`, and `c`.  Prove both inverse laws in each
case.  Prove equality of the generated
relations on the round disk, then use
`Homeomorph.refl` on representatives to obtain the quotient homeomorphism.
For `t97A01`, instantiate the word `a b a⁻¹ b⁻¹ c c` and prove the six
vertex identifications listed in its audit.  The consumer supplies its local
quotient comparison; this node exposes the exact relation-respecting maps it
must prove, without importing a problem file.

### B3. Interior open embedding

lean: `PolygonSurfacePiOne.interiorOpenEmbedding (P : PairingData)` : the
restriction of `P.quotientMap` to `{z : Disk | ‖(z : ℂ)‖ < 1}` is an open
embedding, and its range `P.interior` is open in `P.Space`.

uses: B1

status: planned

No generating relation meets the open disk.  Prove injectivity by induction
on `Relation.EqvGen`; every non-reflexive step has boundary norm one.  For
openness, show the saturation of an open subset of the interior is itself,
then use the coinduced quotient topology.  This supplies the representation
boundary omitted by a mere claim that the polygon has an open 2-cell.

### B4. Two-open polygon cover

lean: `PolygonSurfacePiOne.openCover (P : PairingData)` : open subsets `U P`
and `V P` with `U P ∪ V P = Set.univ`, where `U P` deformation-retracts to
`P.center`, `V P` is the image of an annulus containing the boundary, and
`U P ∩ V P` is homeomorphic to `Set.Ioo (0 : ℝ) 1 × Circle`.

uses: B3

status: planned

Choose fixed radii `0 < r₀ < r₁ < 1`: `U` is the image of norm `< r₁`
and `V` the image of norm `> r₀`.  B3 identifies the overlap before any
boundary identifications occur.  Radial scaling contracts `U`; polar
coordinates give the overlap homeomorphism.  Prove every quotient point has
a representative and split on its norm to establish the cover equation.

### B5. Product quotient descent for radial homotopies

lean: `PolygonSurfacePiOne.quotientMap_prod_unitInterval (P : PairingData)` :
`IsQuotientMap (Prod.map id P.quotientMap)` on `unitInterval × Disk`, and
`PairingData.descendHomotopy` for a continuous representative homotopy that
preserves `Relation.EqvGen` at every time.

uses: B1, Mathlib product-quotient results for a locally compact interval

status: planned

Apply the theorem that the product of a quotient map with the identity on a
locally compact space is quotient.  `descendHomotopy` uses the resulting
quotient map once; it must not prove continuity by choosing representatives.

### B6. Puncture-to-boundary deformation retraction

lean: `PolygonSurfacePiOne.punctureDeformationRetract (P : PairingData)` : a
strong deformation retraction of `V P` onto `P.skeleton`, the image of the
boundary circle, fixed pointwise on that skeleton.

uses: B4, B5

status: planned

On an annular representative send radius `r` linearly to `1`, holding the
argument fixed.  Paired boundary representatives remain paired, while
non-boundary representatives are unique by B3.  Use B5 to descend the map
and homotopy.  Check time zero, time one, and boundary fixation before
packaging the homotopy equivalence used by B10.

### B7. Skeleton as an orbit-indexed circle wedge

lean: `PolygonSurfacePiOne.skeletonHomeomorphWedge (P : PairingData)` :
`P.skeleton ≃ₜ
 PointWedgeQuotient.FiniteWedge (PairingOrbit P.pair) Circle`, together
with equations taking each positively oriented arc to its orbit-indexed
circle and each negatively oriented arc to the inverse parametrization.

uses: B1 and its one-vertex hypothesis, finite point-wedge quotient APIs

status: planned

Cut the boundary circle at all vertices.  Each `pair`-orbit of closed arcs
becomes one circle; the one-vertex proof identifies all endpoints with the
wedge point.  Construct the homeomorphism with one leg literally indexed by
each element of `PairingOrbit P.pair`.  Quotient induction constructs the
inverse lift, and quotient soundness identifies precisely the two paired
arc representatives.  Prove both composites on arc representatives.  The
review's square therefore produces a two-element orbit index automatically;
there is no `Unit` label field with which to collapse it.  The signed
coordinate equations are part of the theorem
because B9 cannot recover the boundary word from an unspecified
homeomorphism.

### B8. Fundamental group of the finite circle wedge with coordinates

lean: `PolygonSurfacePiOne.finiteWedgeCircle_pi1 (L : Type) [Fintype L]
[DecidableEq L]` :
`FundamentalGroup (FiniteWedge L Circle) wedgePoint ≃* FreeGroup L`, with
the map of the `l`-th circle loop equal to `FreeGroup.of l`.

uses: reviewed `PointWedgeVanKampen` B6--B8 and B10--B12

status: planned

Induct over a finite enumeration of `L`.  At each successor use the literal
left/right leg equations, then combine free groups by
`coprodFreeGroupEquivFreeGroupSum`.  Transport the final generator indexing
along the enumeration equivalence.  The empty case is the trivial group.

### B9. Boundary-loop word

lean: `PolygonSurfacePiOne.boundaryLoop_word (P : PairingData)` : under B7
and B8, the positive generator of the overlap circle maps to
`P.boundaryWord : FreeGroup (PairingOrbit P.pair)`, the ordered product of
signed arc-orbit generators.

uses: B4, B6, B7, B8

status: planned

Split the overlap circle loop at the finitely many arc endpoints.  Homotope
each radial segment through B6 to the matching boundary arc.  Apply B7's
signed coordinate equations and `FundamentalGroup.map` functoriality; path
concatenation becomes multiplication in cyclic arc order.  Negative signs
give inverses by reversal.  Repeated occurrences of a generator are equal
exactly when their arcs have the same image in the pairing-orbit quotient;
no additional generator identification is possible.
Basepoint changes are along the displayed radial path and are retained
explicitly.

### B10. Van Kampen with one simply connected piece

lean: `PolygonSurfacePiOne.pi1_quotient_normalClosure` : for an open cover
`U ∪ V = univ` with `U`, `V`, and `U ∩ V` path connected and `U` simply
connected,
`FundamentalGroup X x ≃* FundamentalGroup V v /
  Subgroup.normalClosure (MonoidHom.range overlapToV)`.

uses: `twoOpenFundamentalGroupoidPseudopushoutEquivalence` and its
postcomposition naturality, based connector systems, quotient-group universal
properties

status: planned

Transport the groupoid pseudopushout to chosen base objects.  The `U` vertex
group is trivial, so its leg imposes no generators; the overlap leg imposes
exactly the normal closure of its image in `π₁(V)`.  Construct maps in both
directions from the two universal properties and check them on the `V`
coordinate.  Path-connectedness supplies every connector used in the
basepoint transports.

### B11. Polygon presentation theorem

lean: `PolygonSurfacePiOne.polygonSurface_pi1_presentation
(P : PairingData)` :
`FundamentalGroup P.Space P.center ≃*
 PresentedGroup
   ({P.boundaryWord} : Set (FreeGroup (PairingOrbit P.pair)))`.

uses: B4, B6, B7, B8, B9, B10

status: planned

Apply B10 to B4.  Replace `π₁(V)` by
`FreeGroup (PairingOrbit P.pair)` through B6--B8.
The overlap group is infinite cyclic; B9 says its image is generated by
`P.boundaryWord`, so its normal closure is the relator normal closure used by
`PresentedGroup`.  Finally conjugate from the overlap basepoint to `P.center`
along B4's radial path.

### B12. Standard surface specializations

lean: `PolygonSurfacePiOne.nonorientableSurfaceRelator`,
`orientableSurfaceRelator_eq`,
`nonorientableSurface_pi1_presentation (g) (hg : 0 < g)`, and
`orientableSurface_pi1_presentation (g) (hg : 0 < g)`; in particular
`kleinBottle_pi1_presentation` :
`FundamentalGroup StatementSurfaceModels.KleinBottle
  (StatementSurfaceModels.surfacePoint false 2) ≃*
 PresentedGroup ({nonorientableSurfaceRelator 2} : Set (FreeGroup (Fin 2)))`.

uses: B2, B11, `StatementSurfaceModels.surfaceRelator`

status: planned

Reduce both standard theorems to B11 through B2 and simplify the signed
boundary words.  For the Klein bottle, record the literal word
`of 0 * of 0 * of 1 * of 1`; this is the interface used by the already
banked `KleinPresentedGroupCoordinateModel` chain.

Downstream review after removing generic labels: B8 is a theorem about an
arbitrary finite indexing type and is instantiated at `PairingOrbit P.pair`.
B9 uses B7's leg coordinate, so equal generators mean quotient-equal arc
orbits.  B10 is independent of generator representation.  B11 substitutes
the B7--B9 equivalences and therefore has literally one free generator per
pairing orbit.  B12 alone reindexes those generators to `Fin g` or
`Fin g × Bool`, after proving both inverse laws of the relevant equivalence.
No node B8--B12 contains an unconstrained label map.

## Fixtures and acceptance gates

Each node gets a standalone import fixture under build scratch that states
its full public type and compiles without `sorry`.  B3, B5, B7, B9, and B10
also get negative representation tests: an interior equivalence chain cannot
reach the boundary; a representative-dependent homotopy does not descend;
a pairing with two vertex classes is not accepted; the review's square is
checked to produce two distinct elements of `PairingOrbit pair`;
reversing an arc produces an inverse generator; and omitting normal closure
does not typecheck as the target quotient.  The program gates are:

1. `lake build ConstructionTargets.PolygonSurfacePiOne`;
2. `lake env lean ConstructionTargets/PolygonSurfacePiOne.lean`;
3. fixtures for the standard words `aa`, `aabb`, the orientable genus-two
   commutator word, and `a b a⁻¹ b⁻¹ c c`;
4. `#print axioms` for B11 and B12, permitting only standard axioms;
5. comment-stripped no-`sorry` scans and `python3 scripts/statement-registry.py check`.

## Consumer uptake

- `t96J02`: B12 supplies the missing concrete Klein-bottle presentation;
  its remaining route is presentation-to-semidirect normalization and the
  finite-index subgroup classification.
- `t97A01`: its proved homeomorphism to `Surface false 3` uses B12, while its
  local TorusRP2 quotient supplies the B2 comparison and then uses B11; B4,
  B6, and B7 are also the geometric input to its separate homology programme.
- `t92J05`: after compact-surface classification recognizes the frozen
  manifold as the orientable genus-two surface, B12 supplies the required
  one-relator fundamental group.
- `t94J04`: after the same recognition and covering-correspondence steps,
  B12 identifies the base and finite-cover surface groups; this foundation
  does not itself prove classification or equal-index subgroup isomorphism.
- `t97A03`: B8 supplies the free-rank computations for the circle/sphere
  quotient models after their separate deformation-retraction and cover
  classification.  Its covering classification and homology remain outside
  this foundation.

The first formalisation milestone is B1.  B2 and B3 depend only on B1; B4
depends on B3; B5 depends on B1 and may proceed alongside B3--B4; then the
critical path is B6, B7, B8, B9, B10, B11, B12.
