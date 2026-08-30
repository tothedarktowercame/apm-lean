# Topology dependency DAG

Date: 2026-08-30

This is the canonical topology roadmap.  It separates compiled mathematics,
consumer uptake, small remaining constructions, missing shared APIs, and
foundational library programs.  A `sorry` count alone does not determine a
node's state.

The process for electing new work is defined in
`docs/TN-topology-closure-experiments.md`.

The earlier one-placeholder frontier remains available for historical audit on
`qualification/library-loop-t00J02-solver`.  It must not be merged wholesale:
that branch contains experimental t00J02 developments and is not the authority
for banked results.

## Node states

| State | Meaning | Permitted next action |
|---|---|---|
| `BANKED` | Reusable theorem is committed on canonical master and audited | Add consumers or extend the generic API |
| `UPTAKE` | Mathematics is compiled on a reviewed branch or target; a problem-facing import/adapter remains | Independently review, bank canonically, then wire the frozen consumer |
| `LOCAL-GO` | A concrete bounded construction remains | Dispatch one construction with an explicit stop condition |
| `API-GAP` | A precise reusable theorem is absent from Mathlib/project APIs | Design and prototype that theorem outside any final problem |
| `FOUNDATION` | Several coherent theories must be developed together | Maintain a dedicated program with intermediate milestones |
| `SPEC-DEFECT` | The source or frozen statement is false or materially mismatched | Repair both statement and paper trail before proof work |
| `DEFERRED-REP` | The route is valid but representation-specific and less reusable | Preserve results; do not continue automatically |

## Consumer certification rule

A new `ConstructionTarget` should aim to close at least one real problem, or a
separately named frozen branch of a problem, in the same bounded program.  A
target that merely compiles is infrastructure, not yet certified by uptake.

The expected sequence is:

1. state and compile the reusable theorem;
2. audit it independently;
3. specialize it to a named frozen consumer without changing that consumer's
   statement;
4. compile the consumer with fewer placeholders, ideally zero;
5. record the closing commit in this DAG.

Some foundational increments cannot have an immediate closing consumer.  Such
an exception must name its intended consumer, explain the exact remaining
adapter or theory, and have an explicit stop condition.  Repeated creation of
uncertified adapters for the same blocked chain is not progress.

Consumer closure is the final certification, not the only admissible unit of
work.  A scaffold increment may also be banked when it discharges a named
shared edge used by several downstream nodes.  Such an increment must record:

- the representation and coefficient category in which it is stated;
- the declarations it consumes and provides;
- observed consumers separately from proposed consumers;
- an axiom-clean fixture;
- the exact next edge and a stop condition.

Thin aliases and wrappers around an existing theorem do not discharge a
shared edge.  Representation comparisons, naturality squares, chain
homotopies, and generic geometric equivalences do when later arguments would
otherwise have to reconstruct them.

## Edge evidence model

The DAG distinguishes two kinds of edge:

- **observed**: a current import or declaration use on canonical master;
- **proposed**: a concrete consumer location that would use an absent theorem
  or representation comparison.

Proposed edges must name one of `reusable-theorem`,
`representation-comparison`, or `final-adapter`, and carry a stop condition.
The machine-readable form should follow this shape:

```clojure
{:node/id "ConstructionTargets.ProductionOpenCoverMayerVietoris"
 :node/kind :construction-target
 :authority {:path "ConstructionTargets/ProductionOpenCoverMayerVietoris.lean"
             :git-sha "d03946a0"}
 :state :banked
 :representation {:chains :AddCommGrpCat :coefficients :integers}
 :edges [{:to "problem/t95J04"
          :relation :would-consume
          :need :reusable-theorem
          :status :missing
          :stop-condition "product-homology/Kunneth computation of the cover terms is absent"}]}
```

## Shared dependency graph

```text
SINGULAR-SUBDIVISION/EXCISION [BANKED]
       ├── ALEXANDER-WHITNEY DEGREE TWO [BANKED]
       │      └── LOW-DEGREE-CAP [BANKED]
       ├── MANIFOLD-FUNDAMENTAL-CLASS [FOUNDATION]
       │      ├── MODEL-PAIR LOCAL H1 [BANKED]
       │      ├── HOMEOMORPHISM-OF-PAIRS TRANSPORT [BANKED]
       │      ├── RESTRICTED MANIFOLD CHART PAIR [LOCAL-GO]
       │      ├── GLOBAL LOCALIZATION [FOUNDATION]
       │      ├── COVER-DEGREE [API-GAP]
       │      └── POINCARE/THOM COMPARISON [FOUNDATION]
       ├── OPEN-COVER MV SUBCOMPLEX EXACTNESS [BANKED]
       │      ├── BOOLEAN UNION/REASSEMBLY PRESENTATION [BANKED]
       │      ├── INTEGRAL H0 AUGMENTATION/NATURALITY [BANKED]
       │      ├── SIGNED-DIAGONAL MONO/COKERNEL [BANKED]
       │      ├── INTERSECTION-RANGE TRANSPORT AND PRODUCTION
       │      │      SIGNED-ARROW NORMALIZATION [BANKED `d03946a0`]
       │      └── t00A01 HOMOLOGY BRANCH [CLOSED `f5b0e191`]
       ├── CLOSED-GLUING/COLLAR TO OPEN-COVER [FOUNDATION GENERICALLY]
       │      └── SPHERE-EQUATOR QUOTIENT OPEN COVER [BANKED]
       │             ├── PIECE/INTERSECTION HOMOTOPY EQUIVALENCES [BANKED]
       │             ├── QUOTIENT REPRESENTATION TRANSPORT [BANKED]
       │             ├── DEGREE-TWO PROJECTIVE SPLITTING [BANKED]
       │             ├── NONDEGREE HOMOLOGY [BANKED]
       │             └── t96A03 [CLOSED `adcd54a2`]
       └── MAYER-VIETORIS APPLICATIONS [depends on the two edges above]

MANIFOLD-CALCULUS [BANKED MATHLIB SUBSTRATE]
       ├── PRODUCT-COMPLEMENT IMAGE NULLITY [BANKED]
       │      ├── ARBITRARY FINRANK ADAPTER [BANKED]
       │      └── ONE-CHART DIMENSION-DROP NULLITY [BANKED]
       │             └── COUNTABLE CHART RANGE DECOMPOSITION [BANKED]
       │                    ├── DIFFERENTIABLE-ON LOCAL NULLITY [BANKED]
       │                    ├── COMMON TARGET-CHART NULL TRANSPORT [BANKED]
       │                    ├── GLOBAL FIXED-CHART RANGE NULLITY [BANKED]
       │                    └── DIMENSION-GAP MANIFOLD NONSURJECTIVITY [BANKED]
       │                           └── t94J05 [CLOSED `3348f833`]
       ├── CRITICAL-VALUE MANIFOLD SARD [FOUNDATION]
       ├── REGULAR-PREIMAGE/SUBMERSION [FOUNDATION]
       │      ├── TRANSVERSE-PULLBACK [FOUNDATION]
       │      └── PARAMETRIC/RELATIVE TRANSVERSALITY [FOUNDATION]
       └── LOCAL-DIFFEOMORPH CONVERSE [API-GAP]

COVERING-BASIC [BANKED MATHLIB SUBSTRATE]
       ├── PRODUCT COVER [BANKED]
       ├── PULLBACK/BASE-CHANGE [LOCAL-GO]
       ├── ACTION/QUOTIENT TRANSPORT [LOCAL-GO]
       └── EQUIVARIANT GLUING/CLASSIFICATION [FOUNDATION]

MANIFOLD INTEGRATION
       ├── HAUSDORFF SPHERE NORMALIZATION [API-GAP]
       ├── STOKES FOR FROZEN ENCODINGS [FOUNDATION]
       └── SPHERE/BALL MOMENTS [LOCAL-GO after normalization]

CIRCLE/SPHERE INVARIANTS
       ├── CONCRETE LOOP DEGREE AND WINDING [mixed BANKED/UPTAKE]
       ├── COEFFICIENT-CATEGORY NATURALITY [API-GAP]
       ├── SPHERE ORIENTATION NATURALITY [API-GAP]
       └── HOMOLOGICAL CIRCLE-LIFTING CRITERION [FOUNDATION]

VAN KAMPEN / SURFACE FOUNDATIONS
       ├── TWO-OPEN FUNDAMENTAL-GROUPOID PSEUDOPUSHOUT [BANKED]
       │      ├── PATH SUBDIVISION/HOMOTOPY DESCENT [BANKED]
       │      ├── PSEUDOCOCONE STRICTIFICATION [BANKED]
       │      └── CONNECTED-GROUPOID VERTEX RECONSTRUCTION [BANKED]
       ├── TWICE-SPIRAL COLLAR-COVER SPECIALIZATION [UPTAKE]
       │      ├── COLLAR/COVER COORDINATE MAPPING EQUIVALENCE [BANKED]
       │      ├── PUSHOUT REPRESENTATION EQUIVALENCE [BANKED]
       │      ├── FIXED-TARGET SINGLE-OBJECT MAPPING EQUIVALENCE [BANKED]
       │      ├── TARGET-POSTCOMPOSITION NATURALITY [BANKED THROUGH
       │      │      PUSHOUT-REPRESENTATION AND VERTEX-COORDINATE LAYERS]
       │      └── t01J03 PI1 BRIDGE [UPTAKE; TWO FROZEN SORRIES REMAIN]
       ├── GENERIC QUOTIENT AND GLUING PI1 [FOUNDATION]
       ├── SURFACE CUTTING/CLASSIFICATION [FOUNDATION]
       └── INTERSECTION/SELF-INTERSECTION [depends on fundamental classes]
```

The current certified open-cover nodes have these evidence-backed edges.  An
`observed` edge below is an import or declaration use on canonical master; a
`proposed` edge is not a frozen import or a claim of consumer closure.

```clojure
[{:node/id "ConstructionTargets.BooleanTwoCoverScaffold"
  :authority {:git-sha "44d294de"}
  :state :banked
  :edges [{:to "ConstructionTargets.SingularExcision"
           :relation :imports
           :status :observed}
          {:to "ConstructionTargets.ProductionOpenCoverMayerVietoris"
           :relation :imports
           :status :observed}]}
 {:node/id "ConstructionTargets.SingularH0Augmentation"
  :authority {:git-sha "781eed21"}
  :state :banked
  :edges [{:to "ConstructionTargets.T02A06SphereH0"
           :relation :imports
           :declarations [:h0Augmentation_naturality
                          :h0Map_isIso_of_iso_int]
           :status :observed}
          {:to "ConstructionTargets.T00A01MayerVietorisAdapters"
           :relation :consumed-by
           :status :observed}
          {:to "problem/t00A01/homology-bridge"
           :relation :consumed-by
           :status :observed}]}
 {:node/id "ConstructionTargets.SphereEquatorGluingOpenCover"
  :authority {:git-sha "f7399011"}
  :state :banked
  :edges [{:to "ConstructionTargets.T96A03DegreeTwoMayerVietoris"
           :relation :consumed-by
           :declarations [:leftPieceHomotopyEquiv
                          :rightPieceHomotopyEquiv
                          :intersectionPieceHomotopyEquiv]
           :status :observed}
          {:to "problem/t96A03"
           :relation :consumed-by
           :status :observed}]}
 {:node/id "ConstructionTargets.T96A03FrozenQuotientRepresentation"
  :authority {:git-sha "b3b3f153"}
  :state :banked
  :edges [{:to "problem/t96A03"
           :relation :imports
           :declarations [:coordinateEquatorHomeomorph
                          :conjugateEquatorHomeomorph
                          :coordinateGlueRel_iff_equatorGlueRel
                          :coordinateGluingHomeomorph]
           :status :observed}]}
 {:node/id "ConstructionTargets.ProjectiveQuotientExactSplitting"
  :authority {:git-sha "c08f946d"}
  :state :banked
  :edges [{:to "ConstructionTargets.T96A03DegreeTwoMayerVietoris"
           :relation :consumed-by
           :declarations [:shortExactIsoBiprod]
           :status :observed}]}
 {:node/id "ConstructionTargets.T96A03DegreeTwoMayerVietoris"
  :authority {:git-sha "efa4805e"}
  :state :banked
  :edges [{:to "problem/t96A03"
           :relation :imports
           :declarations [:degreeTwoModuleIsoFinThree]
           :status :observed}]}
 {:node/id "ConstructionTargets.T96A03NonDegreeTwoHomology"
  :authority {:git-sha "5aecf0c3"}
  :state :banked
  :edges [{:to "problem/t96A03"
           :relation :imports
           :status :observed}]}
 {:node/id "ConstructionTargets.SignedDiagonalCokernel"
  :authority {:git-sha "915ee169"}
  :state :banked
  :edges [{:to "ConstructionTargets.MayerVietorisExactnessIsZero"
           :relation :imports
           :declarations [:signedDiagonalCokernelIso
                          :cokernel_π_comp_signedDiagonalCokernelIso_hom
                          :signedDiagonal_mono]
           :status :observed}
          {:to "ConstructionTargets.T00A01MayerVietorisAdapters"
           :relation :consumed-by
           :status :observed}
          {:to "problem/t00A01/homology-bridge"
           :relation :consumed-by
           :status :observed}]}]
```

## Scaffold layers and representations

| Layer | Canonical providers | Representation | Exact outgoing edge |
|---|---|---|---|
| Singular-chain trunk | `SingularHomologyConcrete`, `SingularSubdivision` | unnormalized alternating-face chains in `AddCommGrpCat` | relative/excision/MV and concrete computations |
| Relative and excision | `SingularExcision` | ambient `SSet.Subcomplex`, actual `TopCat` subspaces, integral chains | production open-cover MV; closed-gluing comparison |
| Coefficient-category comparison | `IntegralSingularHomologyComparison` | `AddCommGrpCat ↔ ModuleCat ℤ` | integral sphere and circle results |
| Concrete sphere/circle homology | `SphereHomology`, `CircleSingularHomology`, `T02A06Sphere*` | exported mainly in `ModuleCat ℤ` | degree, retract, and obstruction consumers |
| Low-degree operations | `SingularCapLowDegree`, `Intersection` | integral chain cocycles versus finite-dimensional determinant signs | absent cap/fundamental-class/geometric-intersection comparison |
| Chartwise nullity | dimension-drop/chart decomposition/fixed-chart targets | explicit target-chart Haar measure | nonsurjectivity; not intrinsic manifold measure or critical-value Sard |
| Coverings | Mathlib lifting plus product-cover and higher-homotopy targets | evenly-covered maps and explicit lifts | quotient/deck-action classification remains separate |
| Local homology | `ModelPairLocalHomologyOne`, `ChartPairRelativeHomologyTransport` | one-dimensional relative integral homology | oriented-manifold global-to-local fundamental class |
| Open-cover product geometry | radial and Euclidean pole-overlap targets | homotopy equivalences of concrete subtypes | integral MV computation after production arrow normalization |

Important representation decisions:

- `IntegralSingularHomologyComparison` is the intended bridge between
  `AddCommGrpCat` and `ModuleCat ℤ`; do not duplicate integral computations.
- `circleCellularChainComplex` is not definitionally genuine singular chains;
  it needs a cellular-to-singular comparison before topological use.
- `CircleSingularHomology` is stronger and consumed; `CircleHomology`
  duplicates its `H₁ ≅ ℤ` route without the normalized generator.
- `Intersection` and `SingularCapLowDegree` are complementary local and chain
  layers, not competing implementations of the same theorem.
- `TensorHomologySplitReduction` is canonical at `fdc18723`, but currently
  proves only that homotopic factor maps induce equal maps on tensor-complex
  homology.  It does not perform a split reduction and does not provide a
  singular Eilenberg--Zilber comparison or a Kunneth theorem.

## Uptake census

The 2026-08-27 import/declaration traversal found 69 ConstructionTargets:
50 are transitively consumed by frozen problems and 19 have no current frozen
uptake.  Absence of uptake is not by itself a deletion criterion, but it
requires an explicit proposed edge before extension.

High-value unconsumed scaffold includes `SingularCapLowDegree`,
`ChartPairRelativeHomologyTransport`, `ModelPairLocalHomologyOne`, the
open-cover Mayer--Vietoris targets, and the radial pole-overlap targets.
`T02A06HomologyScaffold` appears superseded by the compiled
`T02A06SphereOne`/`SphereHomology` route.  New work should prefer
`CircleSingularHomology` over the duplicate `CircleHomology` presentation.

## Canonical generic infrastructure

These are stable inputs rather than problem placeholders:

- `ConstructionTargets/SingularSubdivision.lean`: affine and vertex
  subdivision, prism identities, iteration, naturality, diameter control, and
  small-chain comparison.
- `ConstructionTargets/SingularExcision.lean`: relative maps, naturality, and
  excision isomorphisms.
- `ConstructionTargets/SingularHomologyConcrete.lean`: concrete relative
  singular chains and pair exact-sequence components.
- `ConstructionTargets/IntegralSingularHomologyComparison.lean`:
  `ModuleCat ℤ`/`AddCommGrpCat` comparison infrastructure.
- `ConstructionTargets/TransverseLinearPair.lean` and
  `ConstructionTargets/TransversePreimageGeometry.lean`: conversion of
  derivative-range transversality to coproduct surjectivity.  These do not
  construct transverse preimages.

## Closure strategy after the F36--F57 memory review

`futon3c/holes/technotes/TN-fable-F36-F57-review.md` reports that the solver
closed most problems it was given, often without using a shelved memory.  The
one fingerprinted cross-problem use mainly confirmed a maximum-modulus API
route already suggested by the problem.  Cross-problem process memories could
still influence what an agent tried, but token fingerprints could not certify
that influence.  These observations do not supply topology proofs.  They do
change how this DAG should schedule proof work.

For topology, a memory, analogous theorem, or previous construction may
nominate a route.  It is not evidence that the route fits the frozen consumer.
Fit is established only by compiling a consumer-facing probe against the
frozen statement and recording the exact residual.

Every new topology campaign now begins with a **closure experiment**:

1. choose one frozen executable placeholder, not a foundational topic;
2. record the shortest plausible route using current canonical declarations;
3. identify at most one absent reusable theorem on that route;
4. write a small consumer-facing probe that reaches the theorem's input and
   output types without assuming the theorem;
5. continue only if the probe shows that theorem would remove the placeholder
   or leave a bounded final adapter;
6. stop after two successive packets that add infrastructure without reducing
   the named consumer residual.

The probe may use recalled material to find declarations, representations, or
proof patterns.  Its report must distinguish:

- **recalled suggestion**: why the route was tried;
- **repository evidence**: declarations and representations that actually
  compile;
- **consumer evidence**: the frozen goal reached by the probe;
- **new theorem**: the single missing edge, with its other named consumers.

This changes the portfolio order:

1. selective uptake of already compiled experimental closures;
2. problem-facing adapters for canonical theorems;
3. one-edge closure experiments for `LOCAL-GO` and `API-GAP` nodes;
4. foundational programs only after a successful probe and at least two named
   consumers;
5. representation-specific development only while it shortens its frozen
   consumer at the same time.

The twice-spiral branch is the immediate test of the stop rule.  It has banked
subdivision descent, a pseudopushout mapping property, connector
reconstruction, pushout representations, a fixed-target `SingleObj` mapping
equivalence, representability candidates, and postcomposition comparisons
through the pushout-representation and vertex-coordinate layers.  Frozen
`t01J03` still has the same two executable placeholders.  No further target-
naturality layer should be added until a consumer-facing probe states the
exact Mathlib theorem (or project theorem) that turns the natural mapping
equivalence into the required chosen-basepoint automorphism-group isomorphism.
If that probe instead exposes a general categorical representability theorem,
that theorem becomes the single candidate edge; otherwise this branch is
`DEFERRED-REP` until a shorter route is found.

## Consolidation queues

### Queue A: canonical banking and uptake

The breadth-first survey produced several mathematically closed branches.
Each item must be checked against canonical master and independently reviewed
before it is marked `BANKED`:

- `t00J01`: exact Circle fibre cardinalities and regularity;
- `t03J06`: capped-cylinder integral and final conjunction;
- `t94J06`: degree-four disk zero obstruction (`CLOSED` at `8efdc321`);
- `t97J06`: Circle noncontractibility consumer;
- `t98A05`: exterior derivatives, simplex integral, circle-period obstruction,
  and final conjunction (`CLOSED` at `446ca982`);
- `t94A10`: solid-angle closedness branch (nonexactness remains separate).

The canonical audit must record, for every item: source commit, owned files,
direct Lean result, focused build, frozen Main result, axiom audit, placeholder
audit, and reviewer.

The 2026-08-27 audit confirmed that every named item in this queue is absent
from canonical `ConstructionTargets/` and exists only on the experimental
solver line.  Accordingly, `UPTAKE` here means selective promotion and review,
not merely adding an import to canonical Main.

First promoted result: `ThreeRetractionObstructionAdapter` was reviewed and
banked in `b61210cf`.  Canonical `t01A03` was independently already closed by
`8ef14798`, so replacing its existing proof with the adapter would be an
unnecessary refactor.

Second promoted result: the three-pair higher-homotopy covering closure was
reviewed and banked in `37524eb4`.  Its exact frozen-facing bijection is
canonical, and frozen `t01J02` was closed without changing its interface in
`3ba7726a`.

The 2026-08-30 closure experiment elected and closed `t97J06`.  Commit
`0ea00fce` selectively promotes only `CircleNoncontractible.{lean,md}` from
historical commit `2343da9e` and feeds the generic theorem directly to the
existing frozen conditional lemma.  Independent Agency review
`invoke-1788087816801-3748-17bef30b` passed direct compilation, focused build,
placeholder, axiom, and scope audits.

### Queue B: bounded reusable constructions

1. Extend the banked generic product-covering constructor only through new
   independent consumers.  It was reviewed and committed as `935fc228`.
2. Add independent consumers for the banked low-degree integral cap module
   `SingularCapLowDegree`; do not merge the expanded t00J02 subdivision file or
   promote its chartwise/survivor structures as generic geometry.
3. Prototype covering pullback/base-change using existing fibre-bundle
   pullback trivializations.
4. Retain chart-coordinate null-set transport; build a separate
   dimension-drop Euclidean image-null theorem before calling it manifold
   Sard.
5. Extract one-face relative simplex extension only if it has a consumer
   outside the t00J02 representation.

### Queue C: concrete local go-nodes

- specialize the banked production-MV sequence only where a consumer already
  supplies an honest open cover and homotopy models for every term;
- sphere and ball moment calculations after a shared measure normalization;
- finite coordinate and derivative calculations already isolated in the leaf
  survey;
- range/subtype transports such as the middle-interval homeomorphism seam;
- problem-facing adapters for results already canonical and reviewed.

These tasks may be parallelized because their statements do not assume a
shared foundational conclusion.

### Queue D: foundational programs

Ranked by demonstrated reuse:

1. intersection-range transport and production open-cover singular-chain
   normalization; the generic closed-gluing/collar comparison remains the
   subsequent foundational layer for consumers without an explicit cover;
2. oriented-manifold fundamental classes and localization;
3. Eilenberg--Zilber and product homology/Kunneth;
4. manifold Sard plus regular-preimage/submersion geometry;
5. manifold integration and Stokes;
6. covering classification and equivariant gluing;
7. Poincare/Thom/intersection comparison;
8. van Kampen and compact-surface foundations.

Each program requires a separate design note and a first milestone that
compiles independently of every final problem.

## Problem clusters

| Cluster | Representative consumers | Current disposition |
|---|---|---|
| Critical-value manifold Sard | `t01A08`, `t01J04`, `t92J07`, `t93A04`, `t96J05` | `FOUNDATION`; dimension-gap nullity does not address these regular-value problems |
| Dimension-gap manifold nullity | closed `t94J05`; nonsurjectivity part of `t95J04` | generic coordinate-nullity and nonsurjectivity chain is `BANKED`; exact Hausdorff nullity in `t95J04` remains separate |
| Regular/transverse preimages | `t00J02`, `t02A07`, `t94A06`, `t97J05` | `FOUNDATION`; begin with boundaryless regular-preimage geometry |
| Fundamental classes/localization | `t00J02`, `t98A02`, `t00A04`, `t01A05` | `FOUNDATION`; `t00A01` instead assumes its punctured pieces are homology balls and needs MV/van Kampen |
| Intersection theory | `t00J02`, `t03J05`, `t93A05`, `t96J06` | depends on fundamental classes and cap/Thom comparison |
| Closed gluing to open-cover MV | closed `t96A03`; homology branch compiled for `t01J03`; `t03J02` remains | production intersection-range comparison is banked; t96A03 supplies explicit sphere-equator geometry; t01J03 now supplies an explicit collared two-open cover and compiled twice-spiral homology table; a generic collar/cofibration comparison remains `FOUNDATION` for consumers such as t03J02 |
| Product homology/Kunneth | `t95J04`, `t96J06`, `t97A04` | `FOUNDATION`; tensor complexes exist, but singular Eilenberg--Zilber and integral Kunneth do not.  This does not block the two `t95J04` comparisons with `S⁶`: commit `54fe6115` closes those conjuncts by a split-retract homology argument without computing product homology |
| Simply-connected spheres/products | partial `t95J04`; duplicated sphere proof in `t02A06` | `BANKED` at `45304f7d`: generic products preserve `SimplyConnectedSpace`, and concrete Euclidean `Sⁿ` is simply connected for `2 ≤ n`; all three `t95J04` simple-connectivity conjuncts compile |
| Covering constructors | `t01A02`, `t01A04`, `t92J06`, `t98A01` | product is bounded; pullback next; gluing deferred |
| Circle degree/lifting | `t91A08`, closed `t94J06`, closed `t97J06`, `t97A02`, `t97J08` | `t94J06` closed through the selectively promoted path-lifting/winding chain and degree-four disk obstruction; `t97J06` closed via generic singular-homology noncontractibility; further consumers still require separate review |
| Sphere orientation/homology | `t02A08`, `t94J08`, `t95J04`, `t98A02` | computations exist; naturality under concrete maps remains |
| Stokes and moments | `t01J06`, `t02A05`, `t94A10`, `t95J05`, `t96J08`; closed `t98A05` | `t98A05` closed through explicit exterior-derivative, simplex-integral, and circle-period calculations; `t94A10` still needs global sphere-period/Stokes nonexactness; the remaining consumers require separate review |
| Surface classification/gluing | `t00A03`, `t01J01`, `t91J05`, `t94J09`, `t99J03` | late `FOUNDATION`; do not reduce recursively yet |
| Two-open van Kampen/descent | `t01J03`; potentially the open-cover branch of `t00A01` | generic two-open fundamental-groupoid descent and pseudococone mapping property are `BANKED`; the twice-spiral fixed-target mapping equivalence is compiled; target-postcomposition coherence and frozen t01J03 uptake remain |

## Specification and ledger corrections

- `t96J07` remains `SPEC-DEFECT`: the implication in the frozen axis
  characterization has incorrect precedence and contradicts the zero vector
  specialization.
- The experimental ledger's claimed `t01A05` connectedness repair is not on
  canonical master.  Canonical `apm_t01a05` still lacks `ConnectedSpace`
  assumptions for both base and cover, so the disconnected-manifold
  orientation defect remains open canonically.
- The former `t03J04` warning about missing separation/connectedness is stale:
  canonical Main now assumes `T2Space X` and `ConnectedSpace X`.
- Canonical `t94J08` avoids the ordinary-homology `S⁰` defect by using
  `T94J08Sphere (n + 1)`; antipodal-degree naturality is still missing.
- Canonical `t95J06` asks only for a homeomorphism with `Circle × Circle`, not
  the diffeomorphism wording of the source.  This weakening should remain
  visible in the statement paper trail.

## t00J02 disposition

`t00J02` is `DEFERRED-REP`, not the elected foundational project.  The four
method surveys are recorded in
`docs/TN-codex-t00J02-strategy.md`.  Revisit it only when either:

- point-avoidance and fundamental-class localization make the local-homology
  route available; or
- regular-preimage orientations and a generic geometric/homological
  comparison make the direct transverse route available.

The experimental geometric-chain route is preserved as research evidence.
Its conditional incidence structures and genus-two-specific calculations are
not substitutes for those missing generic interfaces.

The continuous MV campaign gives a quantitative contrast without claiming
that commit count measures mathematical difficulty.  The production chain
from `1906ef4e` through `d03946a0` contains 25 banked commits; six subsequent
reusable representation/consumer commits from `a44c1396` through `43a492da`
resolved H₀ nonemptiness, coefficient coordinates, subspace-map equality, and
the frozen adapters; one consumer commit, `f5b0e191`, then closed an actual
frozen homology bridge.  The subsequent t96A03 certification from
`f181ffa2` through `adcd54a2` contains 19 commits: 11 extend the explicit
sphere-equator gluing geometry, six bank reusable normalization, splitting,
representation, and homology results, and two wire the frozen quotient and
final theorem.  Thus this scaffold campaign has closed one frozen homology
branch and one whole frozen problem.  The earlier t00J02 program remains four
surveyed experimental tracks with no frozen theorem closure and with its
generic orientation/localization producers still absent.  This comparison
supports continuing consumer-certified shared scaffolds; it does not show
that the MV route solves t00J02 or replace its missing geometry.

## Banked consolidation increments

| Commit | Reusable result | Remaining consumer work |
|---|---|---|
| `935fc228` | product evenly-covered trivializations and `IsCoveringMap` closure | instantiate in concrete covering consumers |
| `b61210cf` | three generic retraction obstructions, including the categorical integral-H1 form | reusable infrastructure; `t01A03` was already closed independently in `8ef14798` |
| `3c96f98e` | `H₁(B¹, B¹ \ {0}; ℤ) ≅ ℤ`, named nonzero local generator, and radial pair-map transport | transport through a manifold chart; global fundamental-class localization remains foundational |
| `b94fdc26` | degree-two Alexander--Whitney front/back edges, chain maps, boundary formula, and naturality | extract the now-unblocked low-degree cap module |
| `1f0a8882` | image nullity for differentiable `E → E × G` with nontrivial finite-dimensional complement | add explicit linear-equivalence/complement transport, then combine with chart-null transport |
| `408be02b` | integral singular one-cocycles, low-degree cap operations, Leibniz identities, homology descent, and naturality | add independent consumers; manifold fundamental-class comparison remains foundational |
| `20191b38` | arbitrary strict-finrank differentiable image nullity via an explicit finite-dimensional complement equivalence | combine with chart-coordinate null transport; then prove the manifold chart-cover statement |
| `37524eb4` | cube-boundary path connectivity and covering-induced higher-homotopy bijectivity | consumed by closed `t01J02` in `3ba7726a` |
| `ce5839a7` | one-chart strict-finrank nullity, fixed-chart countable unions, and differentiable chart-change transport | consumed by the countable range-decomposition layer; no canonical manifold measure is asserted |
| `707efa05` | relative singular homology isomorphism for a homeomorphism of pairs and nonzero transport of the model local generator | construct the restricted manifold chart pair and its deleted-point equivalence |
| `fb05ffe9` | countable source/target chart-pair patches, full range decomposition, and exact coordinate equation | prove local `DifferentiableOn` dimension-drop nullity and compare varying target-chart null sets |
| `7c2f83a6` | strict-finrank image nullity for maps differentiable only on the source subset | consumed by the manifold coordinate-patch theorem |
| `b4d6065f` | transport varying extended-chart null patches into any fixed target chart and assemble the countable union | consumed by fixed-target-chart global range nullity |
| `7e531b1d` | fixed-target-chart range nullity for `C¹` strict-dimension-drop manifold maps | consumed by the boundaryless target nonsurjectivity theorem |
| `0193d098` | fixed-chart coordinate nullity contradicts surjectivity for boundaryless targets | consumed by closed `t94J05`; reusable for the nonsurjectivity component of `t95J04` |
| `3348f833` | specialization of the dimension-gap chain to smooth `T² → S³`, followed by the existing missed-point contraction | frozen `t94J05` closed with statements unchanged |
| `44d294de` | Boolean two-cover with definitionally aligned union and reassembly arrows | construct the intersection-range chain isomorphism and its two inclusion naturality squares; no production MV theorem yet |
| `781eed21` | canonical integral `H₀` augmentation, naturality, and isomorphism of induced `H₀` maps between nonempty spaces explicitly identified with `ℤ` | transport the production MV degree-zero maps through these coordinates; no connectedness inference or t00A01 bridge is claimed |
| `bb7a7c67` | dimension-generic sphere-equator quotient open cover, equatorial-band contraction, and three restricted quotient maps | completed by the quotient-descended homotopy-equivalence chain through `f7399011` and consumed by closed t96A03 |
| `915ee169` | signed diagonal is monic and has cokernel canonically isomorphic to its coefficient object, with quotient projection equal to the codiagonal | representation normalization was completed by the later t00A01 adapter chain |
| `d03946a0` | complete production open-cover Mayer--Vietoris exactness with actual intersection, reassembly, union, and connecting arrows | consumed by the t00A01 adapters and frozen homology bridge; closed-gluing consumers still need their own open-cover geometry |
| `a44c1396`–`c75a86a3` | H₀ nonemptiness detection, conjugated signed-diagonal cokernel coordinates, and canonical equality between simplicial and production subspace-inclusion maps | consumed by `T00A01MayerVietorisAdapters`; these resolve representation seams rather than add new homology assumptions |
| `c59a4dd9`, `43a492da` | reusable t00A01 MV adapters for H₀, top connecting isomorphisms, coefficient transport, and actual production H₀-arrow monicity | observed import and declaration use in frozen t00A01 at `f5b0e191` |
| `f5b0e191` | frozen `apm_t00A01_bridge_connectedSum_isHomology3Sphere` assembled from the production MV chain and adapters | homology branch closed; van Kampen bridge and final conjunction remain executable placeholders |
| `f181ffa2`–`f7399011` | explicit source decompositions, coherent quotient-descended deformations, retractions, and homotopy equivalences for both sphere pieces and their equatorial intersection | consumed by the reusable t96A03 Mayer–Vietoris calculations; this is concrete quotient geometry, not a generic closed-gluing theorem |
| `21301fae`, `c08f946d` | rank-three `ModuleCat ℤ` normalization and generic splitting of a short exact sequence with projective quotient | consumed by the degree-two t96A03 calculation |
| `c6b6a239`, `b3b3f153` | positive-dimensional equator nonemptiness and explicit frozen/coordinate sphere-equator representation transport | consumed by the frozen t96A03 quotient homeomorphism and final homology assembly |
| `5aecf0c3`, `efa4805e` | all nondegree homology groups of the reusable gluing model and its actual degree-two production-MV short exact sequence, projective split, and `Fin 3` normalization | imported by frozen t96A03 at `adcd54a2` |
| `f6cfdaf8`, `adcd54a2` | frozen quotient identified with the reusable equator-gluing model, followed by complete homology transport in every degree | `t96A03` closed with zero executable placeholders |
| `8fbcdbd2`–`4973b3c0` | subdivision-independent and homotopy-invariant two-open path evaluation, descent functor, strictified pseudococone equivalence, and the two-open fundamental-groupoid pseudopushout mapping property | generic API is banked; it is observed by the twice-spiral collar-cover specialization, but no ordinary strict `Limits.Pushout` theorem is asserted |
| `4c807ccf`–`fca9b574` | explicit twice-spiral collared cover, transport to boundary/solid-torus coordinates, and equivalence between ambient mapping functors and coordinate pseudococones | fixed-target mapping equivalence is compiled; source-groupoid equivalence still requires target-postcomposition naturality |
| `5dcc68f5`–`f983be62` | connector normal forms for connected groupoids, vertex-data and integer-coordinate equivalences, `TwiceSpiralPushout d` representation equivalence, and identification with functors from `SingleObj (TwiceSpiralPushout d)` | yields a fixed-target equivalence `(FundamentalGroupoid (Gluing h) ⥤ C) ≃ (SingleObj (TwiceSpiralPushout d) ⥤ C)`; it does not by itself identify the source groupoids |
| `6413a6cb`–`c862ae93` | representability candidates and target-postcomposition comparisons for the pushout-representation and vertex-coordinate layers | pause further coherence layers until a consumer probe identifies the exact representability-to-source-equivalence theorem needed by frozen t01J03 |
| `fdc18723` | homotopy invariance of tensor-complex homology maps in either factor | map-level algebraic input only; despite the filename, no split reduction is implemented, and product-topology consumers still need singular Eilenberg--Zilber and coefficient-compatible Kunneth comparisons |

## Dimension-gap versus critical-value Sard

The banked dimension-drop chain is useful when
`finrank ℝ sourceModel < finrank ℝ targetModel`.  It is not a proof of general
critical-value Sard.

- Direct first consumer: `t94J05`, closed in `3348f833`.  It uses
  nonsurjectivity of a smooth two-dimensional-to-three-dimensional manifold
  map and the previously compiled missed-point contraction.
- Partial consumer: the nonsurjectivity component of `t95J04`; its exact
  ambient Hausdorff-measure statement still needs a measure-comparison theorem.
- Not consumers of this branch: `t93A04`, `t01A08`, `t01J04`, and `t96J05`.
  They need regular values of maps without a strict source/target dimension
  gap, hence the separate critical-value Sard program.  `t01J04` additionally
  lacks the second-countability assumption used by the chart-cover chain.

## Problems closed during consolidation

| Problem | Canonical closure | Audit result |
|---|---|---|
| `t01A03` | `8ef14798` | no executable placeholders; only standard axioms |
| `t01J02` | `3ba7726a` using `37524eb4` | status `solved`, zero placeholders, statements unchanged, only standard axioms |
| `t94J05` | `3348f833` using the banked dimension-gap chain | status `solved`, zero placeholders, statements unchanged, only standard axioms |
| `t00A01` homology branch | `f5b0e191` using `d03946a0`, `c59a4dd9`, and `43a492da` | bridge placeholder removed; frozen statement unchanged; whole problem is not closed because van Kampen and final assembly remain |
| `t96A03` | `adcd54a2` using the sphere-equator geometry through `f7399011`, quotient adapter `b3b3f153`, and homology targets `5aecf0c3`/`efa4805e` | status solved, zero placeholders, frozen statement unchanged, only standard axioms |
| `t97J06` | `0ea00fce` using the selectively promoted generic `CircleNoncontractible.circle_not_contractible` | zero placeholders, frozen statement unchanged, direct/focused builds passed, independent Agency review passed, only standard axioms |
| `t94J06` | `8efdc321` using six selectively promoted circle-lifting/winding and degree-four disk-obstruction targets | two placeholders removed, frozen statements unchanged, historical blobs verified byte-for-byte, direct/focused/frozen builds passed, independent Agency review passed, only standard axioms |
| `t98A05` | `446ca982` using six selectively promoted exterior-derivative, simplex-integral, and circle-period targets | four placeholders removed, frozen statements unchanged, historical blobs verified byte-for-byte, direct/focused/frozen builds passed, independent Agency review passed, only standard axioms |

Bounded partial closures, which do not belong in the closed-problem table:

| Problem | Canonical partial closure | Remaining frozen obligation |
|---|---|---|
| `t95J04` | `54fe6115` compiles `S⁶ ≄ S² × S⁴` and `S⁶ ≄ S³ × S³`; `45304f7d` adds generic simply-connected sphere/product theorems and compiles all three simple-connectivity conjuncts.  Both packets passed separate Agency election, implementation, and review chains | one placeholder remains only for Sard/nullity/non-surjectivity/null-homotopy and `S² × S⁴ ≄ S³ × S³`; statement unchanged |

Current audited classification beyond these closures:

- `t00J02` and `a97J08` are `UPTAKE`: each has one genuine geometric producer
  remaining, respectively oriented-surface duality and planar separation.
- Frozen `t96A03` is `CLOSED` at `adcd54a2`.  Its solution uses the explicit
  sphere-equator quotient geometry and does not supply the generic
  collar/cofibration comparison still missing for `t03J02` and `t97A01`;
  those problems remain `API-GAP`.
- The homology branch of `t00A01` is `CLOSED` at `f5b0e191`: the frozen file
  imports and uses the production MV API and representation adapters.  The
  whole problem remains `FOUNDATION`/API-stopped because its independent van
  Kampen bridge is absent; the final conjunction remains unwired until that
  bridge exists.  `t95J04` also remains `FOUNDATION`, although its two
  comparisons with `S⁶` are now compiled at `54fe6115` by the independent
  retract argument.
- `t01J03` is `UPTAKE`, not closed.  Its torus results, explicit collared
  quotient geometry, and twice-spiral module-homology computation compile.
  The generic two-open fundamental-groupoid pseudopushout and the specialized
  fixed-target mapping equivalence are banked.  Two executable placeholders
  remain in frozen `Main.lean`: `apm_t01J03_bridge_2`, which still needs the
  source-groupoid/fundamental-group extraction, and the final conjunction
  `apm_t01j03`.  Target-postcomposition naturality is being proved because a
  family of fixed-target mapping equivalences alone does not justify the
  source-groupoid equivalence.
- `t03J02` is stopped before implementation: its `IsEmbedding` and
  `Nullhomotopic` hypotheses do not provide the collar/NDR neighbourhood needed
  by production Mayer--Vietoris, and its fundamental-group branch separately
  needs van Kampen.  The explicit t01J03/t96A03 bands are not generic evidence
  for an arbitrary embedded circle.
- `t97J06` is `CLOSED` at `0ea00fce`.  Its existing conditional reduction to
  `¬ ContractibleSpace Circle` now consumes the selectively promoted generic
  theorem; independent review job `invoke-1788087816801-3748-17bef30b`
  confirmed zero placeholders and unchanged statements.
- `t94J06` is `CLOSED` at `8efdc321`.  Its generic radius-disk bridge and final
  radius-seven specialization now consume the selectively promoted
  circle-lifting/winding chain.  Election job
  `invoke-1788091410408-3755-148461f2`, implementation job
  `invoke-1788091783980-3759-e0d38d5c`, and independent review job
  `invoke-1788092071400-3763-78a77595` establish `2 → 0` placeholders with
  unchanged frozen statements.
- `t98A05` is `CLOSED` at `446ca982`.  Election job
  `invoke-1788094173427-3862-c9a2987f` verified one coherent six-module packet;
  implementation job `invoke-1788094520582-3901-ed650d94` closes all four
  frozen placeholders, and independent review job
  `invoke-1788094761055-3915-1d0e382a` passed source-integrity, mathematical,
  compilation, placeholder, axiom, and scope audits.
- `t96J07` remains `SPEC-DEFECT` and must not receive proof scaffolding before
  statement repair.

## Next decision point

The initial closure experiments are complete; their Agency job ids and full
decisions are recorded in `docs/TN-topology-closure-experiments.md`.

1. **CLOSED: `t97J06` by selective uptake.**  Implementation job
   `invoke-1788087615270-3747-34cc93a0` produced `0ea00fce`; independent review
   job `invoke-1788087816801-3748-17bef30b` passed.  No further work remains on
   this consumer.
2. **STOP: `t01J03` representability.**  The first missing edge is target-
   postcomposition naturality for the generic pseudococone equivalence.  The
   source-reconstruction theorem would be a second absent edge.  Do not resume
   the transport chain from the later algebraic layers.
3. **PARTIAL: `t95J04`; STOP remains on its product foundation.**  Election
   `invoke-1788088998881-3750-c29c22f9`, implementation
   `invoke-1788089170654-3751-711e3944` (`54fe6115`), and independent review
   `invoke-1788089485653-3752-a094d808` compile the two `S⁶` versus product
   clauses via a split retract.  The later `45304f7d` packet compiles all three
   simple-connectivity clauses.  The single frozen placeholder now remains
   only for Sard and `S² × S⁴ ≄ S³ × S³`.
   Singular Eilenberg--Zilber and integral Kunneth remain two independent
   absent foundations; do not restart them from this partial closure.
4. **STOP: `t03J02` generic gluing.**  The frozen hypotheses provide neither a
   collar/NDR pair nor van Kampen.  A collar requires the absent
   Jordan--Schoenflies theory, and the two explicit coordinate covers do not
   generalize to an arbitrary embedded circle.

Return to the portfolio rather than continuing any stopped chain
automatically.  The bounded `t95J04` retract adapter has completed its full
election, implementation, and review chain; it does not elect the remaining
product-homology program.

The second portfolio round likewise elected exactly one closure:

5. **STOP: `t00J01` selective fold uptake.**  Probe
   `invoke-1788091405247-3753-2e843c2e` verified the circle-fold branch but
   found two independent residual foundations: the concrete Klein-product
   manifold/top-homology bridge and rational sphere Lefschetz normalization.
6. **STOP: `t03J06` capped-cylinder uptake.**  Probe
   `invoke-1788091407907-3754-d9387d48` verified the `7π` integral packet, but
   smoothness and the exterior-derivative value remain a separate missing
   theorem.  Do not promote the integral chain as a consumer closure.
7. **CLOSED: `t94J06` degree-four disk obstruction.**  Probe
   `invoke-1788091410408-3755-148461f2` elected one coherent six-module chain;
   implementation `invoke-1788091783980-3759-e0d38d5c` produced `8efdc321`,
   and independent review `invoke-1788092071400-3763-78a77595` passed all
   source-integrity, compilation, placeholder, axiom, and scope gates.

No round-two result elects either stopped residual program automatically.

The third portfolio round also elected exactly one closure:

8. **CLOSED: `t98A05` explicit differential-form calculations.**  Probe
   `invoke-1788094173427-3862-c9a2987f` elected a coherent six-module packet;
   implementation `invoke-1788094520582-3901-ed650d94` produced `446ca982`,
   and independent review `invoke-1788094761055-3915-1d0e382a` passed with
   placeholders `4 → 0` and unchanged frozen statements.
9. **STOP: `t94A10` solid-angle uptake.**  Probe
   `invoke-1788094176057-3863-3bbcc70b` verified the historical closedness
   chain, but nonexactness independently needs global sphere-period/Stokes or
   de Rham comparison.  Do not promote the eighteen-file partial packet as a
   consumer closure.
10. **STOP: `t97J08` winding reuse.**  Probe
    `invoke-1788094178560-3864-3adb8687` verified that canonical winding
    infrastructure closes uniqueness and that cross derivatives compile, but
    the beta-integral comparison still needs `C¹` regularity of the covering
    lift.  Do not infer differentiable regularity from continuous path lifting.

No round-three result elects either stopped residual program automatically.

11. **PARTIAL: `t95J04` simply-connected spheres/products.**  Generic product
    probe `invoke-1788096708714-3934-ec4a501e`, Euclidean-sphere probe
    `invoke-1788096711721-3935-2177b3f1`, and consumer probe
    `invoke-1788096714421-3936-144a4823` all returned `ELECT`.
    Implementation `invoke-1788097093918-3940-4f798b6e` produced `45304f7d`;
    fresh independent review `invoke-1788097372302-3941-269150b7` passed.
    All three simple-connectivity conjuncts are compiled, while the one frozen
    placeholder remains only for Sard and `S² × S⁴ ≄ S³ × S³`.

This construction does not elect either remaining `t95J04` foundation.

The banked production-MV scaffold already supplies:

- radial equivalences for punctured normed spaces and concrete two-pole sphere
  complements, including product transport;
- public chain- and homology-level naturality for range subcomplex inclusions
  and cover members;
- homology-biproduct normalization and generic exactness-to-vanishing lemmas.

The Boolean scaffold and the subsequent representation-normalization chain
now state production open-cover Mayer--Vietoris exactness with actual arrows
in `d03946a0`.  The former intersection-range and `eqToIso` stops are closed;
future consumers must supply their own open-cover geometry and term
computations.

For t00A01, that calculation is now observed in the frozen theorem at
`f5b0e191`: overlap `H₂`, ball vanishing, signed-diagonal monicity/cokernel,
and H₀ augmentation discharge every homology degree.  This closes only the
homology branch.  The independent van Kampen theorem remains absent.

For t96A03, the geometry chain through `f7399011` supplies the three required
homotopy equivalences; `b3b3f153` and `f6cfdaf8` transport the frozen quotient
to that reusable model; `5aecf0c3` and `efa4805e` compute every homology degree.
The frozen theorem imports those targets and closes at `adcd54a2` with zero
placeholders.  This is an observed consumer edge, not evidence for a generic
closed-gluing theorem.
