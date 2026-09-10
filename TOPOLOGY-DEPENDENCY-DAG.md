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
       │      └── t01J03 PI1 BRIDGE [CLOSED `7ddf3408`]
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

The twice-spiral branch validated the stop rule.  It banked
subdivision descent, a pseudopushout mapping property, connector
reconstruction, pushout representations, a fixed-target `SingleObj` mapping
equivalence, representability candidates, and postcomposition comparisons
through the pushout-representation and vertex-coordinate layers.  Consumer-
facing probes then showed that pointwise target-change squares suffice for
source reconstruction, avoiding an unnecessary pseudonaturality program.
Reviewed commits `338011a6`, `86d454aa`, and `a8974ed7` supplied the source
equivalence, compatible connectors, and chosen-object extraction; frozen
closure `7ddf3408` removes both remaining placeholders.

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
| Critical-value manifold Sard | closed `t93A04`, closed `t92J07`; `t01A08`, `t01J04`, `t96J05` have separate uptake records | Genuine-smooth Euclidean and manifold-to-vector Sard are `BANKED`; `t93A04` closed at `a49c8476`, with exact reusable extraction `337bdd48`; `t92J07` closed at `b364803a` by predicate equality and countable common-value assembly. Historical missing-infrastructure STOP evidence is retained. General-model/target-manifold transport and regular-preimage geometry remain separate. |
| Dimension-gap manifold nullity | closed `t94J05`, closed `t95J04` | coordinate-nullity chain is `BANKED`; `a13852f3` closes literal sphere Hausdorff nullity, nonsurjectivity and null-homotopy in `t95J04`; its open-domain Hausdorff helper is embedded in Main, not a separately extracted module |
| Regular/transverse preimages | `t00J02`, `t02A07`, `t94A06`, `t97J05` | `FOUNDATION`; begin with boundaryless regular-preimage geometry |
| Fundamental classes/localization | `t00J02`, `t98A02`, `t00A04`, `t01A05` | `FOUNDATION`; `t00A01` instead assumes its punctured pieces are homology balls and needs MV/van Kampen |
| Intersection theory | `t00J02`, `t03J05`, `t93A05`, `t96J06` | depends on fundamental classes and cap/Thom comparison |
| Closed gluing to open-cover MV | closed `t96A03` and `t01J03`; `t03J02` remains | production intersection-range comparison is banked; t96A03 supplies explicit sphere-equator geometry; t01J03 supplies an explicit collared two-open cover and complete twice-spiral computation; a generic collar/cofibration comparison remains `FOUNDATION` for consumers such as t03J02 |
| Product homology/Kunneth | `t96J06`, `t97A04` | `FOUNDATION`; tensor complexes exist, but singular Eilenberg--Zilber and integral Kunneth do not.  `t95J04` no longer consumes this missing foundation: `54fe6115` handles the two `S⁶` comparisons by retracts, and `e24d442b`--`10cfb866` handle `S² × S⁴ ≄ S³ × S³` through one concrete production Mayer--Vietoris segment |
| Simply-connected spheres/products | closed `t95J04`; duplicated sphere proof in `t02A06` | `BANKED` at `45304f7d`: generic products preserve `SimplyConnectedSpace`, and concrete Euclidean `Sⁿ` is simply connected for `2 ≤ n`; all three conjuncts are retained in the complete `t95J04` closure `a13852f3` |
| Covering constructors | `t01A02`, `t01A04`, `t92J06`, `t98A01` | the generic product cover was already banked; reviewed `c5ada212` now closes the concrete `(ZMod 2)²` covering-group branch of `t01A02`; fivefold AddCircle kernel cardinality/deck packaging is next for `t98A01`; pullback and gluing remain separate |
| Circle degree/lifting | closed `t91A08`, closed `t94J06`, closed `t97J06`, closed `t97A02`, closed `t97J08` | `t91A08` closed through the power-five winding obstruction and exact additive-circle transport at `02b4e476`; `t94J06` closed through path lifting/winding and the degree-four disk obstruction; `t97J06` closed via singular-homology noncontractibility; `t97J08` closes the smooth-lift/angle-integral chain at `0ad32428`; `t97A02` closed at `69fd2f35` through finite-H1 loop triviality, constructed component lifts and exact torus recombination (independent PASS `invoke-1788977263821-16745-f3b25cde`, placeholders `2 → 0`); further consumers require separate review |
| Smooth circle lifts | closed `t97J08`; reusable smooth circle maps with continuous real lifts | generic local-inverse regularity `48eab2d3`, explicit `Circle.exp` specialization `12fd086d`, and normalized-loop specialization `55da22d8` are `BANKED`; frozen consumer closed at `0ad32428` |
| Sphere orientation/homology | `t02A08`, `t94J08`, `t95J04`, `t98A02` | computations exist; naturality under concrete maps remains |
| Stokes and moments | `t01J06`, `t02A05`, `t94A10`, `t95J05`, `t96J08`; closed `t98A05` | `t98A05` closed through explicit exterior-derivative, simplex-integral, and circle-period calculations; `t94A10` still needs global sphere-period/Stokes nonexactness; the remaining consumers require separate review |
| Surface classification/gluing | `t00A03`, `t01J01`, `t91J05`, `t94J09`, `t99J03` | late `FOUNDATION`; do not reduce recursively yet |
| Two-open van Kampen/descent | closed `t01J03` | the reviewed chain through `fca797fa` proves pointwise target naturality of the existing gluing-to-`SingleObj` mapping equivalence; `338011a6` reconstructs the source equivalence, `86d454aa` supplies compatible connectors, `a8974ed7` extracts the chosen-object group, and `7ddf3408` performs the frozen homeomorphism/basepoint transport and final assembly |

## Specification and ledger corrections

- `t96J05` is a local `SPEC-DEFECT`, not a missing-Sard closure edge.
  The reviewed centered-unit-circle counterexample satisfies every frozen
  hypothesis, but every inhabited radial level is the circle and cannot
  carry the required zero-dimensional atlas. Independent PASS:
  `invoke-1788996921425-17341-4294c07a`. The exact fixture, frozen hash and
  unchanged one-placeholder count are recorded in
  `holes/labs/topology-contract/evidence/t96j05-radial-level/BOUNDARY.md`.
  Banked Euclidean fiber geometry does not supply an attained regular radius.
  A corrected statement needs an explicit decision about attained regular
  levels or permitted empty levels; no repair is chosen and Main is unchanged.
  This local refutation is neither consumer closure nor campaign termination;
  all older counterexamples and uncovered cases below remain in force.
- `t96J07` has reviewed **corrected closure** at
  `6f475b3c40e2a2528a0efd7e17c89f8f1af904a7`, PASS
  `invoke-1789002417270-17501-59e6c3e7`. Exactly two added statement
  parentheses put the axis equivalence under the nonzero-vector implication;
  placeholders decreased `1 → 0` in that implementation. The old frozen
  clause remains false at zero, with its refutation preserved verbatim.
  This is specification repair plus corrected closure, not unchanged frozen
  closure or an intrinsic projective-derivative comparison. See
  `problems/t96J07/STATEMENT-REPAIR.md` and the corrected-closure record in
  `docs/TN-topology-closure-experiments.md`.
- The experimental ledger's claimed `t01A05` connectedness repair is not on
  canonical master.  Canonical `apm_t01a05` still lacks `ConnectedSpace`
  assumptions for both base and cover, so the disconnected-manifold
  orientation defect remains open canonically.
- The former `t03J04` warning about missing separation/connectedness is stale:
  canonical Main now assumes `T2Space X` and `ConnectedSpace X`.
- `T94J08Sphere k` is the unit sphere in ambient dimension `k`, so
  `T94J08Sphere (n + 1)` is Sⁿ and does **not** avoid S⁰ at `n = 0`.
  The old ordinary-H₀ statement is exactly refuted (codex-12, independently
  passed by codex-10). On 2026-09-09 the owner-authorized specification repair
  re-freezes the ordinary-homology branch at `1 ≤ n`, and its local-index
  specialization at `1 ≤ m` (ambient dimension at least two). This branch
  retains the existing positive-dimensional sphere orientation/naturality route;
  it remains open with two placeholders. The S⁰ / one-dimensional local-index
  cases need a separately elected reduced-homology encoding. Neither that
  outstanding coverage nor the old refutation is erased or counted as closure.
  See `holes/labs/topology-contract/evidence/t94j08-zero-sphere/REPAIR.md`.
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

## Reviewed t97A02 closure

`t97A02` is **CLOSED** at `69fd2f354468e1409b979d75818a1d01cf727e6c`.
Independent review `invoke-1788977263821-16745-f3b25cde` returned `PASS`.
Canonical integral coefficient comparison and Circle Hurewicz naturality
turn finite H1 into trivial induced loops. Component normalization, actual
inclusion naturality and covering lifts construct real lifts; open-component
assembly includes empty domains, and the existing product homotopy theorem
recombines the coordinates into the exact frozen torus conclusion.

The historical STOP `invoke-1788970466031-16587-aad35f58`, independently
validated by `invoke-1788970813855-16596-55365337`, was an API/construction
boundary, not a refutation. `ClassicalLocalPathConnectivity` at `f8d3d381`
and `ComponentRealLiftAssembly` at `0322d72b` resolved that boundary before
the final adapter constructed its component lifts. No stronger local
contractibility or global path connectivity was assumed.

The closing commit reduced executable placeholders **2 → 0** with original
signatures unchanged. Fixture and frozen statement hashes, reviewed build
results, and standard-axiom audits are recorded in the
[t97A02 process account](docs/TN-topology-closure-experiments.md#t97a02-reviewed-closure).
This documentation update contributes zero additional placeholder reduction
and certifies no other consumer.

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
- Closed consumer: `t95J04` at `a13852f3`. This chain supplies nonsurjectivity;
  local Lipschitz Hausdorff-dimension estimates, countable chart aggregation
  and the sphere inclusion isometry separately prove its literal measure claim.
- Not consumers of this branch: `t93A04`, `t01A08`, `t01J04`, and `t96J05`.
  They need regular values of maps without a strict source/target dimension
  gap, hence the separate critical-value Sard program.  `t01J04` additionally
  lacks the second-countability assumption used by the chart-cover chain.

## Problems closed during consolidation

| Problem | Canonical closure | Audit result |
|---|---|---|
| `t95J04` | `a13852f35c671f0d40d4bbf58e832710563a4ef7` | independent PASS `invoke-1789000811470-17453-38632ef7`; all original definitions, lemma bodies and final statement preserved; placeholders `1 → 0`; warning-free, standard-only axioms |
| `t92J07` | `b364803ac4e0c6b2d20d06d9c937f1f0a9892eb4` using the extracted manifold Sard theorem | independent PASS `invoke-1788994194142-17263-038c93a8`; frozen definitions and both statements unchanged; placeholders `2 → 0`; standard axioms and unused-`hm` warning only; zero-target branch retained |
| `t93A04` | `a49c84764968d8286ff05d87e5d218018505f50c`; reusable extraction `337bdd48a1770df37cd2ed8cb48fea924f4203cd` | frozen definitions and statement preserved; placeholders `1 → 0`; independent PASS `invoke-1788993199960-17228-ce848168`; extraction PASS `invoke-1788993593682-17243-48fdadcf`, not a second closure; standard axioms and inherited unnecessarySimpa warning only |
| `t01A03` | `8ef14798` | no executable placeholders; only standard axioms |
| `t01J02` | `3ba7726a` using `37524eb4` | status `solved`, zero placeholders, statements unchanged, only standard axioms |
| `t94J05` | `3348f833` using the banked dimension-gap chain | status `solved`, zero placeholders, statements unchanged, only standard axioms |
| `t00A01` homology branch | `f5b0e191` using `d03946a0`, `c59a4dd9`, and `43a492da` | bridge placeholder removed; frozen statement unchanged; whole problem is not closed because van Kampen and final assembly remain |
| `t96A03` | `adcd54a2` using the sphere-equator geometry through `f7399011`, quotient adapter `b3b3f153`, and homology targets `5aecf0c3`/`efa4805e` | status solved, zero placeholders, frozen statement unchanged, only standard axioms |
| `t97J06` | `0ea00fce` using the selectively promoted generic `CircleNoncontractible.circle_not_contractible` | zero placeholders, frozen statement unchanged, direct/focused builds passed, independent Agency review passed, only standard axioms |
| `t94J06` | `8efdc321` using six selectively promoted circle-lifting/winding and degree-four disk-obstruction targets | two placeholders removed, frozen statements unchanged, historical blobs verified byte-for-byte, direct/focused/frozen builds passed, independent Agency review passed, only standard axioms |
| `t98A05` | `446ca982` using six selectively promoted exterior-derivative, simplex-integral, and circle-period targets | four placeholders removed, frozen statements unchanged, historical blobs verified byte-for-byte, direct/focused/frozen builds passed, independent Agency review passed, only standard axioms |
| `t97J08` | `0ad32428` through local-inverse regularity `48eab2d3`, `Circle.exp` regularity `12fd086d`, and normalized-loop lift regularity `55da22d8` | four placeholders removed, frozen statements unchanged, every milestone independently reviewed, historical blobs verified, seven-module/frozen build passed, only standard axioms |
| `t01J03` | `7ddf3408` through source reconstruction `338011a6`, connector existence `86d454aa`, and chosen-object extraction `a8974ed7` | two placeholders removed, frozen statements unchanged, exact zero-placeholder fixture compiled, final frozen review passed, only standard axioms |
| `t91J02` | `628f5131` using `CircleUniversalCover.circleFundamentalGroupMulEquivInt` and `SimplyConnectedSphereProducts.euclideanSphere_simplyConnected` | sole placeholder removed, literal sphere/basepoints unchanged, direct/focused builds and independent review passed, only standard axioms |
| `t91A05` | `3f3b72b2` using the shared `CircleMetricFundamentalGroup` adapter | two placeholders removed, metric-sphere carrier and basepoint align definitionally with bundled `Circle`, frozen statements unchanged, independent review passed, only standard axioms |
| `t97J03` | `3f3b72b2` using the shared `CircleMetricFundamentalGroup` adapter | sole placeholder removed, norm-one subtype and basepoint align definitionally with bundled `Circle`, frozen statement unchanged, independent review passed, only standard axioms |
| `t91A08` | `02b4e476` using the reviewed power-five winding obstruction and exact `AddCircle.homeomorphCircle` transport | two placeholders removed, frozen statements unchanged, direct/full builds and independent Zai review passed, four warnings are pre-existing, only standard axioms |
| `t02A03` | `61f8ece4` through point-wedge geometry, production Mayer--Vietoris, target-natural free-product representation, generic source reconstruction, and frozen quotient transport | three placeholders removed across reviewed commits (`301501c2`/`7ea2c595`, then `61f8ece4`); both final frozen statements unchanged, zero warnings, full build and independent review passed, only standard axioms |

Bounded partial closures, which do not belong in the closed-problem table:

| Problem | Canonical partial closure | Remaining frozen obligation |
|---|---|---|
| `t01A02` | `c5ada212` imports the banked genuine product-cover theorem and compiles the coordinatewise `(ZMod 2)²` action, invariance, freeness, and fiber transitivity | three placeholders remain: H₂ degree/nonsurjectivity, Lefschetz fixed point, and final assembly; covering-group bridge statement unchanged |
| `t92J05` | `c55d5089` compiles uniform sphere-group subsingletonity and uniform circle-group equivalences at arbitrary basepoints | three placeholders remain: the RP²/antipodal bridge, genus-two classification bridge, and final assembly; whole problem remains open |

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
  bridge exists. `t95J04` is now closed at `a13852f3`; its earlier retract,
  simple-connectivity and MV proofs are retained unchanged.
- `t01J03` is `CLOSED` at `7ddf3408`.  Its reviewed chain derives the source
  groupoid equivalence from pointwise target-change squares, constructs the
  required connector systems, extracts the chosen-basepoint fundamental
  group as `Multiplicative (ZMod 2)`, transports across the frozen gluing
  homeomorphism, and reuses the banked module-homology computation.  Both
  frozen statements are unchanged and both placeholders are removed.
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
- `t96J07` has reviewed corrected closure at `6f475b3c`, PASS
  `invoke-1789002417270-17501-59e6c3e7`, after the explicit two-parenthesis
  statement repair. Its historical false-statement refutation is retained;
  this documentation update contributes no additional placeholder reduction.

## Next decision point

The initial closure experiments are complete; their Agency job ids and full
decisions are recorded in `docs/TN-topology-closure-experiments.md`.

1. **CLOSED: `t97J06` by selective uptake.**  Implementation job
   `invoke-1788087615270-3747-34cc93a0` produced `0ea00fce`; independent review
   job `invoke-1788087816801-3748-17bef30b` passed.  No further work remains on
   this consumer.
2. **CLOSED after staged revision: `t01J03`.**  The initial representability
   experiment stopped correctly before unsupported source reconstruction.
   Later consumer-facing probes compiled each adjacent target-change square,
   established that pointwise squares suffice, and closed the frozen problem
   at `7ddf3408` after independent review.
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

## Medium-depth queue

1. **CLOSED: `t97J08` smooth lift and angle integral.**  Program probe
   `invoke-1788099827204-4008-8baa6eb6` led to four separately reviewed
   milestones, ending at `0ad32428` with placeholders `4 → 0`.  Smoothness was
   derived through an explicit local inverse, never from `IsCoveringMap` alone.
2. **PARTIAL COMPLETE: `t95J04` MV product comparison.**  Probe
   `invoke-1788099830885-4009-cfbf41e5` led to reviewed commits `e24d442b`,
   `6b59e2e6`, `f8feca24`, and `10cfb866`.  All three nonhomeomorphism and all
   three simple-connectivity conjuncts now compile without Kunneth or
   Eilenberg--Zilber.  The sole frozen residual is the Sard branch.
3. **CLOSED: `t01J03` target postcomposition and source extraction.**  Probe
   `invoke-1788099833859-4010-0cd0ae16` returned `GO`.  First bank
   `postcomposePseudoFunctorCoconeFunctor` and the generic pseudopushout
   comparison natural isomorphism.  That first milestone is reviewed at
   `67aa463e` (implementation `invoke-1788104723752-4333-30cd2f57`, review
   `invoke-1788104940330-4335-18ef87b5`).  Probe the immediately following
   equivalence layer before further implementation.  Probe
   `invoke-1788105082590-4338-c2585085` identified that layer and reviewed
   prerequisite commit `bc5267e9` supplies coordinate-pseudococone
   postcomposition plus the collared generic specialization.  Elect the
   forward comparison only after its full glue square compiles.  That theorem
   is now reviewed at `74ae0e1e` (probe
   `invoke-1788105858496-4358-28fcb259`, implementation
   `invoke-1788106366249-4370-8c228d74`, review
   `invoke-1788106925596-4385-37a16353`).  The inverse-direction mate is now
   reviewed at `a81dad87` (probe `invoke-1788107112060-4389-f5f223e8`,
   implementation `invoke-1788107362539-4396-63e454e1`, review
   `invoke-1788107623205-4401-9486e9f6`).  Probe connector/basepoint
   vertex-data naturality next.  That square is now reviewed at `789eb675`
   plus repair `7d9cd14a` (probe `invoke-1788108001589-4406-6d487aff`,
   implementation `invoke-1788108286633-4413-081764bd`, repair
   `invoke-1788113281009-4459-01ddd48f`, combined re-review
   `invoke-1788115696208-4486-15d12b7a`).  The later algebraic comparisons are
   now composed at reviewed commit `f1a217ab` (probe
   `invoke-1788115854743-4489-444a6bf7`, implementation
   `invoke-1788116169840-4496-82729c6a`, review
   `invoke-1788116426273-4498-a75f6346`).  The final consumer-facing paste is
   reviewed at `fca797fa` (probe `invoke-1788116682320-4519-851404a0`,
   implementation `invoke-1788116841342-4523-15360639`, review
   `invoke-1788117042204-4524-8abccc3e`).  Probe
   `invoke-1788118997109-4548-f36e2e28` established that pointwise squares
   suffice; source reconstruction is reviewed at `338011a6` after exact
   fixture-provenance repair and re-review
   `invoke-1788126570453-5141-771c2de6`.  Extract the chosen-object
   endomorphism group next.  The first extraction probe
   `invoke-1788126694360-5151-b2ac96a3` compiled the group equivalence but
   returned `REVISE` because frozen data did not yet provide
   `LegCompatibleConnectorSystems`.  Geometry probe
   `invoke-1788127015351-5176-bbe5dda0` reduced that gap to a dependent
   connector-extension equality; focused probe
   `invoke-1788127419504-5214-cd187779` compiled the complete constructor.
   Agency job `invoke-1788132709346-5391-2b521a94` implemented it at
   `86d454aa`; independent review `invoke-1788132913624-5392-17335c93`
   returned `PASS`.  At that milestone frozen `t01J03` still had exactly two
   placeholders, so the chosen-object adapter was compiled and reviewed before
   any frozen edit.
   Agency job `invoke-1788134364506-5394-61f849ef` implemented that generic
   extraction at `a8974ed7`; independent review
   `invoke-1788134519264-5395-fcedd5c8` returned `PASS`.  The remaining probe
   is frozen-facing only: transport the chosen basepoint through
   `apm_t01J03_homeomorph_gluing`, instantiate the coordinate data, and test
   the exact `bridge_2` and final conjunction proofs before editing `Main`.
   Frozen-facing probe `invoke-1788134727903-5396-89a31181` compiled the exact
   `Main` with placeholders `2 → 0`.  Agency implementation
   `invoke-1788134993841-5397-e9ad42bb` committed the one-file closure at
   `7ddf3408`; independent review `invoke-1788135236814-5398-4213fd16`
   returned `PASS`.  Statements are unchanged, direct/focused builds pass,
   and both completed theorems use only standard axioms.
4. **PARTIAL COMPLETE: `t01A02` product covering group.**  Balanced-program
   probe `invoke-1788166722963-5399-9b32f06b` found the generic genuine
   product-cover theorem already banked and compiled both torus
   specializations.  Agency job `invoke-1788167439562-5404-c87746d4`
   implemented the four-element sign action and frozen covering-group bridge
   at `c5ada212`; independent review
   `invoke-1788168053258-5407-be3b1f19` returned `PASS`.  Frozen placeholders
   decreased `4 → 3`; the H₂ degree and Lefschetz branches remain independent.
5. **STOP: `t00A01` generic van Kampen.**  Probe
   `invoke-1788166722968-5401-75be2e99` compiled factorwise coproduct
   transport and final assembly, but the generic theorem collapsing a
   two-open fundamental-groupoid pseudopushout with simply connected overlap
   to a vertex-group free product was absent.  Focused probe
   `invoke-1788168504079-5411-c64fa9bb` found that this is not one bounded
   theorem: canonical master separately lacks (a) the generic equivalence
   between functors from a connected groupoid and functors from the
   `SingleObj` category of a chosen vertex group, and (b) collapse of a
   simply-connected-overlap pseudococone to free-product representations.
   Target-natural composition and source reconstruction would follow as a
   third stage.  Do not implement partial connector or `Monoid.Coprod`
   wrappers as though they close the frozen bridge.
6. **Historical STOP: manifold Sard (t93A04 subsequently closed).**  Probe
   `invoke-1788166722965-5400-bccfd117` compiled fixed-chart criticality and
   critical-image inclusion for `t93A04`, but pinned Mathlib only supplies an
   equal-dimensional determinant Sard theorem.  Do not promote those partial
   chart lemmas or begin countable assembly before a rectangular local-set
   Morse--Sard theorem handles arbitrary finite source dimension.
   This records the dependency boundary at that probe, not a mathematical
   refutation or the current status: reviewed closure `a49c8476` subsequently
   discharged the frozen consumer using genuine-smooth Sard and actual chart
   criticality transport. See the closure evidence below.

### Reviewed t95J04 closure evidence (2026-09-10)

Canonical commit `a13852f35c671f0d40d4bbf58e832710563a4ef7` and independent
codex-10 PASS `invoke-1789000811470-17453-38632ef7` certify complete frozen
closure, with placeholders `1 → 0`, no warnings, and only `propext`,
`Classical.choice` and `Quot.sound`. Original definitions, lemma bodies and
the final statement are preserved. Verified canonical Main/fixture SHA-256:
`81a52f4f97d8d47874c34dd610c8ed500f11e873439b1276b3ca08348e0f6ea6`;
frozen pre-closure SHA-256:
`8321b881ae48f14a9d5e711534aa208eabd66dcdc16055f5ce22e9b66ce4fc15`;
unchanged `apm_t95j04` statement SHA-256:
`4411a00266690b8196b64d48fd645c39ad27e922eb3fb8d6d2f62da64ba5f2db`.

Actual chart representatives give local Lipschitz Hausdorff-dimension bounds;
countable aggregation and the sphere subtype isometry give the literal sphere
Hausdorff nullity. Separate coordinate nullity gives nonsurjectivity, and the
preserved missed-point contraction gives null-homotopy. Empty and
zero-dimensional sources require no extra assumptions.
`ConstructionTargets.OpenDomainHausdorffNullity.image_null` is embedded in
the consumer file, not a separately extracted reusable module.

Earlier partial results remain provenance: `54fe6115` (two sphere/product
comparisons), `45304f7d` (simple connectivity), and `e24d442b`, `6b59e2e6`,
`f8feca24`, `10cfb866` (MV product comparison). Historical STOP and partial
entries record their then-current boundaries, not the present closed status.
Other consumers' product foundations, representation and specification
boundaries remain open. This documentation changes no Lean file and counts
neither a second closure nor another placeholder reduction.

### Reviewed t92J07 closure evidence (2026-09-09)

Commit `b364803ac4e0c6b2d20d06d9c937f1f0a9892eb4` closes the complete
common-regular-value consumer. Independent codex-10 PASS
`invoke-1788994194142-17263-038c93a8` verifies exact one-file promotion,
unchanged definitions and statements, and executable placeholders `2 → 0`.
The frozen `criticalValues` predicate equals the image of the actual
nonsurjective-mfderiv locus. Reused `T93A04ManifoldWork.null_critical` gives
nullity; the existing countable common-value theorem and frozen regular-fiber
equivalence close every literal fiber certificate. The zero-target branch
is unchanged, and no source nonemptiness or positive dimension is added.

- Frozen source SHA-256: `413b97f2d2b2075305818c6c25d5db79744aa95aa5b5c04762c146033d2740fe`.
- Closure fixture `/tmp/T92J07FullClosure.lean` and current source SHA-256: `0e7bf95466e914d03b456449f5605abd35a49df231aa4c6fef4d0edbedc943e3`.
- Unchanged `apm_t92J07_bridge_1` statement SHA-256: `5da05c37abf248a169fd810c3e66d794b7e173e9771594077b1e8fc8481bacee`.
- Unchanged `apm_t92j07` statement SHA-256: `50d85b6512de9021ccacdab5476c51f9f0bfe299945caf00faa130994202b977`.

Both reviewed compilations use only `propext`, `Classical.choice`, and
`Quot.sound`. The sole warning is unused `hm` in the preserved bridge
signature: the imported theorem also covers zero-dimensional targets.
This is one distinct consumer closure, not another t93A04 closure or an
infrastructure count; this documentation adds no further placeholder delta.
Historical STOP records remain evidence of their then-missing infrastructure.
General-model/target-manifold transport and actual regular-preimage atlas,
embedded inclusion and tangent-image geometry remain separate obligations,
not residual hypotheses of the closed t92J07 theorem.

### Reviewed t93A04 closure evidence (2026-09-09)

Closure `a49c84764968d8286ff05d87e5d218018505f50c` was independently
approved by codex-10 in `invoke-1788993199960-17228-ce848168`.
Actual source-chart criticality transport and countable null-image aggregation
give a regular projection value; the projection kernel and frozen
range-plus-span bridge prove the literal affine-line transversality predicate.
Empty and zero-dimensional sources require no added assumptions.

- Frozen source SHA-256: `4431ba028376d7a85867bd9ec81e3ac94a64d891661c7ee149701461a56d3fea`.
- Unchanged `apm_t93a04` statement SHA-256: `854fea2e1c0bd60b27caee326f218fa4dd639f9dcc3791fe9975dbe9990e7e11`.
- Closure fixture `/tmp/T93A04Closed.lean` and committed consumer SHA-256: `ca834f20b42db9742d8b4c90b6ab7fb8364ee8dcf617a59df97d02c623437bbd`.
- Extraction `337bdd48a1770df37cd2ed8cb48fea924f4203cd`, independently approved in `invoke-1788993593682-17243-48fdadcf`, preserves `T93A04ManifoldWork.null_critical` exactly in `ConstructionTargets/SardGenuineSmoothManifoldVector.lean` (SHA-256 `ff63bdc1e857973e9b2cecc345e9e2fab37aefd81973718267a1ee50fe7dd951`).
- Importing consumer fixture `/tmp/T93A04ManifoldReuse.lean` and current source SHA-256: `5baf0e7d27ecb11934c0862e5955cedca42e307deed38ab569d31a90eb8c2f83`; its tail is byte-identical to the closure consumer after the extracted producer.

Executable placeholders decreased `1 → 0` at closure and stayed `0 → 0`
at extraction. Both reviews reproduced only `propext`, `Classical.choice`,
and `Quot.sound`, with the inherited `unnecessarySimpa` warning in
`lineDirection_ne_zero`. Extraction is reuse, not a second closure.
General target-manifold chartwise transport and regular-preimage global atlas,
embedded inclusion and tangent-image geometry remain downstream obligations;
they are not residual hypotheses of the closed t93A04 theorem.

## Strategy reset after the first topology closure campaigns

Three Agency surveys ran in parallel.  Whole-closure survey
`invoke-1788190476663-5737-717318b3` found no GO in its initial shortlist;
`t01A02`, `t03J04`, and `t94J09` each retain two independent edges.  Reuse
survey `invoke-1788190476668-5739-90db9f55` searched beyond that shortlist and
compiled complete closures for `t91J02`, `t91A05`, and `t97J03`.  Foundation
survey `invoke-1788190476664-5738-b21d2d26` nominated oriented fundamental
classes/localization, with regular-preimage atlas construction as backup.

The first elected immediate closure was `t91J02`.  Agency job
`invoke-1788191087925-5750-0a283098` implemented the exact one-file proof at
`628f5131`; independent review `invoke-1788191275394-5753-3dac9f3a` returned
`PASS`.  Frozen placeholders decreased `1 → 0` and the statement is unchanged.
The shared metric/unit-circle follow-up probe
`invoke-1788191632892-5757-5444c31a` then compiled one explicit transported
winding class and simultaneous zero-placeholder fixtures for `t91A05` and
`t97J03`.  Implementation job `invoke-1788192224009-5761-e0847d10` committed
the exact four-file packet at `3f3b72b2`; independent review
`invoke-1788192667431-5763-86f56a1e` returned `PASS`.  The two literal circle
representations and their basepoints reduce to the bundled `Circle` data
without conjugation, frozen statements are unchanged, and placeholders
decrease `2 → 0` and `1 → 0`.  Both problems are **CLOSED**.

The nominated foundation program has four bounded milestones: integral local
orientation/fundamental-class data with chart-change and localization;
transverse circle pairing or Thom localization; proof of
`OrientedSurfacePreimageDuality.Producer S`; and frozen `t00J02` wiring.  Hard
stop after milestone 1 if the local class cannot enter the actual
`singularHomologyFunctor (ModuleCat ℤ)` representation without another
general excision, cellular comparison, or cohomology-ring foundation.  This
program remains nominated but inactive; closing the Circle-reuse consumers
does not activate it automatically.

## Zai strategy reset and `t91A08` closure

Three read-only Zai surveys supplied the next portfolio.  Whole-closure survey
`invoke-1788215060969-6109-cfb4b864` found the power-five circle obstruction;
reuse survey `invoke-1788215060973-6110-f8882aee` compiled bounded partial
bridges for `t02A03` and `t92J05`; foundation survey
`invoke-1788215060976-6111-45142ecd` refined the oriented-localization first
milestone to the explicit computation `H₂(D², S¹; ℤ) ≅ ℤ` with a nonzero
generator in the actual integral singular-homology representation.

The initial `t91A08` report compiled only the `Circle` theorem, so it was not
sent directly to implementation.  Focused probe
`invoke-1788215789052-6122-260cc550` compiled the complete frozen
`UnitAddCircle` fixture with placeholders `2 → 0`.  Implementation job
`invoke-1788217406776-6150-50dba411` committed the exact one-file closure at
`02b4e476`; independent review `invoke-1788217609118-6154-e144c1ec` returned
`PASS`.  The proof uses path-lift uniqueness and endpoint-winding invariance
to distinguish power five from identity on `Circle`, then conjugates both maps
through `AddCircle.homeomorphCircle` with the canonical `toCircle_nsmul`
orientation.  Statements are unchanged and no new warnings or axioms appear.
`t91A08` is **CLOSED**.

The first queued reuse bridge was then implemented.  Fixture
`/tmp/probe-t02A03-bridge1.lean` compiled the exact torus fundamental-group
statement.  Agency job `invoke-1788217963425-6167-cd4aa038` committed the
one-file uptake at `301501c2`; review
`invoke-1788218127747-6171-0e8bd3c1` caught that the named
`MulEquiv.prodMultiplicative` equivalence was written in its reverse declared
orientation even though definitional compatibility let Lean accept it.
Repair job `invoke-1788218477039-6181-dedc119b` committed the explicit `.symm`
at `7ea2c595`; combined re-review
`invoke-1788218568346-6185-ee63858e` returned `PASS`.  The bridge statement is
unchanged and placeholders decrease `3 → 2`.  This is a bounded partial
closure only: wedge van Kampen/homology and final assembly remain.

The oriented degree-two disk-pair program remains nominated but inactive.  Its
hard stop is any need for a new general excision theorem, cellular comparison,
or cohomology ring before the first milestone enters `ModuleCat ℤ`; a second
stop applies after two consecutive infrastructure packets that do not reduce
the literal `t00J02` producer residual.

The second queued reuse bridge was implemented by Agency job
`invoke-1788218818205-6189-8001f99f` at `c55d5089`; independent review
`invoke-1788218993463-6194-711fe6db` returned `PASS`.  The proof installs
simple connectivity on the literal `Fin 3` sphere uniformly in its basepoint,
constructs path connectivity for the literal complex metric circle, transports
an arbitrary circle basepoint to `metricCircleHomeomorphCircle.symm 1`, and
then applies the reviewed winding equivalence in the forward direction.  The
bridge statement is unchanged and placeholders decrease `4 → 3`.  This is a
bounded partial closure only: the RP²/antipodal bridge, genus-two
classification bridge, and final assembly remain.

Focused `t02A03` construction surveys then isolated a shared first dependency:
an honest open-cover model for the literal point-wedge quotient.  Geometry
probe `invoke-1788250899585-6693-a30e4ca3` compiled the generic EqvGen
saturation theorem and exact quotient-image preimage equality in
`/tmp/PointWedgeSaturation.lean`.  Implementation job
`invoke-1788251341798-6703-7c75de42` promoted the generic quotient and
saturated-open-cover skeleton at `7cfa9888`; independent review
`invoke-1788251536399-6707-cb73a819` returned `PASS`.  Openness is proved by
rewriting the coinduced preimage to the original saturated open set, not by
assuming that quotient maps send arbitrary opens to opens.  This milestone
does not yet claim the punctured-circle contraction, the three cover homotopy
equivalences, Mayer--Vietoris, free-product π₁, or frozen closure.

The next geometry probe `invoke-1788251718932-6708-ad04df18` compiled an
explicit pointed contraction of `Circle \ {-1}` and its product.  The
stereographic coordinate sends the chosen basepoint `1` exactly to zero, so
the scalar contraction fixes that basepoint at every time rather than relying
on an arbitrary contractibility witness.  Implementation job
`invoke-1788252461798-6713-eb4b1719` promoted the generic structure, circle
and product contractions, and literal punctured-torus neighborhood
homeomorphism at `ac910fb4`; independent review
`invoke-1788252660981-6715-e4e9ac55` returned `PASS`.  Wedge descent, the
concrete cover, Mayer--Vietoris, source reconstruction, and frozen uptake
remain separate milestones.

The subsequent cover-assembly probe `invoke-1788252830639-6717-c2611c10`
isolated one further generic prerequisite: descending a pointed contraction of
the right summand through the point-wedge quotient.  Fixture
`/tmp/PointWedgePointedContractionDescent.lean` (SHA-256
`bcfcb58cdecbc0bea7f28da100d7eb15436629dd7fefa6956b55ad908c6087b2`)
compiled the quotient collapse, left inclusion, jointly continuous descended
deformation, and representative formulas.  Agency implementation
`invoke-1788253180184-6719-4d22cede` promoted the exact generic pair at
`8bc28a2d`; independent review `invoke-1788253421696-6721-67ac9471` returned
`PASS`.  The proof uses the pointed contraction's fixed-basepoint law at the
sole generated wedge relation and pulls joint continuity back along
`id × quotientMap`; its homotopy runs from the quotient identity to left
inclusion after collapse, with the required reversal used in the equivalence
law.  The remaining geometry milestone is still the concrete restricted-wedge
assembly for `U`, `V`, and `U ∩ V`, including the frozen adapter and all three
homotopy equivalences.  Mayer--Vietoris, free-product source reconstruction,
and frozen `t02A03` closure remain later dependencies.

The next restricted-cover probe `invoke-1788253603416-6724-4d5dffe3`
returned `REVISE` rather than treating a continuous bijection as a quotient
homeomorphism.  It compiled the exact generic restriction theorem in
`/tmp/PointWedgeRestrictedOpenQuotient.lean` (SHA-256
`35c776fc9784539ff7272a90f47af92040fd00ea5a5ff471e0f04cfd12bfc138`):
the canonical quotient map restricted over a saturated open image remains an
`IsQuotientMap`.  Agency job `invoke-1788253885565-6726-b392c489` promoted
that target at `c5b6f9cd`; independent review
`invoke-1788254069917-6729-0a427d7c` returned `PASS`.  The proof uses
`IsQuotientMap.restrictPreimage_isOpen` together with the reviewed literal
preimage equality.  The next dependency is the generic homeomorphism between
that restricted quotient subtype and the point wedge of the two restricted
summands, including formulas on both representatives; concrete `U/V`, their
intersection, and the three homotopy equivalences still follow afterward.

The first `restrictedOpenHomeomorphWedge` probe
`invoke-1788254214027-6732-26985a9d` isolated the last coproduct-level
prerequisite.  Fixture `/tmp/ProbePre.lean` (SHA-256
`cc433af68701863cb43715ad4d07bd6a4ffcec8d356fa2489acad92edc23b8d7`)
compiled an honest homeomorphism from the subtype of the restricted coproduct
to `A ⊕ B`, using the two open subtype embeddings and the exact range of
`Sum.map Subtype.val Subtype.val`.  Agency job
`invoke-1788254708777-6736-ba09bfcc` added it and its two representative
formulas at `17d8e69e`; independent review
`invoke-1788254857707-6738-c716c7dd` returned `PASS`.  No basepoint or quotient
claim is hidden in this result.  The quotient-level restricted-wedge
homeomorphism remains the next typed theorem.

The quotient-level re-probe `invoke-1788255086508-6741-acb1a42a` then
compiled the complete restricted-wedge homeomorphism in
`/tmp/RestrictedWedgeProbe.lean` (SHA-256
`5e3c5a399a58f032b08f3f02569b84f8696f71e28426e3b5fc0eeccba4722b88`).
It constructs both quotient directions, proves continuity through the two
reviewed quotient-map `continuous_iff` theorems, proves both inverse laws on
representatives, and exports formulas in both directions plus the glued
basepoint identities.  Agency job `invoke-1788255630673-6747-98b29cf4`
promoted the construction at `f2394dd6`; independent review
`invoke-1788255810934-6750-61aa4313` returned `PASS`.  The generic restricted
point-wedge topology layer is therefore complete.  The next geometry packet
must specialize it to the actual punctured torus/circle opens, derive the
symmetric contraction orientation, identify the intersection, transport the
frozen quotient, and compile the three cover homotopy equivalences.

Concrete cover re-probe `invoke-1788255951621-6753-56dfc906` compiled that
entire geometry packet in `/tmp/TorusCircleWedgeOpenCoverProbe.lean` (SHA-256
`b2a0c568d01aae80e504590893e19dd4569811beef9c38c1d2e06507efb9138d`).
It gives the literal punctured-circle and punctured-torus neighborhoods,
actual open `U/V`, their cover and exact intersection, three restricted-wedge
models, a generic wedge swap, right contraction derived through that swap,
and homotopy equivalences of `U`, `V`, and `U ∩ V` with the torus, circle,
and `Unit`.  The fixture also compiled the identity-on-representatives frozen
adapter.  Agency implementation `invoke-1788256591051-6758-fa7a8fbc`
promoted the reusable pair at `0fc1cb8c`; independent review
`invoke-1788256790027-6763-01146072` returned `PASS`.  Frozen-only relation
names were correctly omitted from the ConstructionTarget.  Point-wedge open
geometry is therefore reviewed; the next dependency is the actual-arrow
Mayer--Vietoris calculation and frozen homology transport.

Mayer--Vietoris probe `invoke-1788256983740-6765-e7d695ad` compiled the full
generic homology table and frozen transport in `/tmp/TorusCircleWedgeH0.lean`
(SHA-256
`bfd4e682efc5672f8b5ba05cdcc79e64b8e07375facdf19e06555cfae4161452`).
Agency implementation `invoke-1788257581180-6768-414bb19a` promoted the
generic calculation at `31d0d05c`.  Initial review
`invoke-1788257831963-6772-700165fb` correctly found that the chosen `Fin 3`
normalization put the circle coordinate first despite documentation claiming
the reverse.  Repair `invoke-1788258049081-6775-9a8f359c` introduced an
explicit torus-first equivalence at `61e03da1`, with definitional equations
for coordinates 0, 1, and 2.  Combined re-review
`invoke-1788258422939-6779-54235657` returned `PASS`.  The reviewed theorem
computes `H₀ = ℤ`, `H₁ = ℤ³` with torus coordinates first, `H₂ = ℤ`, and
zero homology above degree two from the actual production MV arrows.  The
homology branch of frozen bridge 2 is therefore ready for later local
transport; only free-product fundamental-group reconstruction remains before
the consumer packet.

The remaining π₁ probe `invoke-1788258601115-6781-367fc638` reached a
genuine `STOP`.  Fixture
`/tmp/TorusCircleWedgeFundamentalGroupoidProbe.lean` (SHA-256
`8c371411deb527fb607e56956a2d771bab394d3831bfbfb2e319f819c19304e9`)
compiled the actual two-open fundamental-groupoid pseudopushout and its
arbitrary-target postcomposition naturality for the reviewed wedge cover.
Three independent constructions remain: generic transport of pseudococones
through equivalences of groupoid spans and compatible 2-cells; a target-natural
mapping equivalence representing the point-span pseudococones by
`SingleObj (Monoid.Coprod G H)`, normalized on both coproduct injections; and
comparison of the reconstructed inverse with the literal inclusion-induced
coproduct map together with the frozen EqvGen quotient adapter.  The t01J03
versions of the first two layers are specialized to its solid-torus coordinate
span and algebra.  No implementation is elected: fixed-target equivalences,
assumed bijectivity, or coordinate-specific reuse would not prove the frozen
statement.  `t02A03` therefore remains open with its homology branch reviewed
and its free-product π₁ branch stopped at this foundation boundary.

A resumed first-layer probe `invoke-1788274848206-6902-72f97e5d` refined that
boundary with executable evidence.  The independently recompiled fixture
`/tmp/GenericSpanPseudoCoconeForwardProbe.lean` (SHA-256
`7cc86daede18f781beb3ab218a71fbabf2c91feee8f7416eef5afcbed3a9b96c`)
constructs the fully generic forward pseudococone transport functor and its
arbitrary-target postcomposition natural isomorphism, with only `propext`,
`Classical.choice`, and `Quot.sound`.  Two independent constructions still
separate it from an equivalence usable by the wedge: generic reverse transport
with unit/counit glue squares, and concrete comparison 2-cells showing that
the chosen `U/V/UV` homotopy equivalences commute with the actual overlap
inclusions.  The second obligation is not implied by contractibility of the
overlap.  Work beyond the compiled forward functor is blocked on those two
theorems; no source-reconstruction claim is made.

The first coherence dependency was then split and completed.  Probe
`invoke-1788275855211-6907-a563a1c6` compiled four arbitrary-natural-iso
round-trip lemmas in `/tmp/EquivalenceSpanRoundTripIsoProbe.lean` (SHA-256
`42f3e4d536875826f2c9d13fca9d8de347c072596432b8fa6024ccffff0b58c6`).
Implementation `invoke-1788276678690-6912-4aa8bc75` committed them at
`9aebc3da`; review `invoke-1788277045001-6915-40a763c0` found that the rewrite
had removed equality-valued public names used by the canonical twice-spiral
consumer.  Compatibility repair `invoke-1788277228320-6917-ae8d0340`
restored the historical helpers and theorem signatures alongside the new API
at `2e436010`; combined re-review
`invoke-1788277672856-6920-a3b9e1da` returned `PASS`, including a successful
build of `TwiceSpiralPseudococoneTransport`.  The generic reverse transport
milestone can now use arbitrary comparison isomorphisms without regressing the
coordinate-specific consumer.  Pseudococone unit/counit assembly, the
equivalence triangle, and reverse/equivalence-level target naturality remain
the next categorical packet.

Unit/counit glue probe `invoke-1788278063040-6925-59c98a8f` reduced both
orientations to one shared reassociation law.  Fixture
`/tmp/GenericSpanWhiskerReassociationProbe.lean` (SHA-256
`ce9ba311d1adac57d0f5203b4211306f04926d97e8e14384664dbcc0f8029846`)
compiled generic preservation of a three-factor natural-transformation
composite by left whiskering.  Implementation
`invoke-1788278445726-6929-ac0b954d` added the theorem at `ec9cc067`;
independent review `invoke-1788278649478-6932-424d2971` returned `PASS` and
rebuilt the existing twice-spiral consumer.  The objectwise pseudococone
unit/counit glue squares are now ready for a focused re-probe.

`t92J05` remains open on its independent surface-classification foundations.
The former `t02A03` van Kampen boundary was subsequently closed by the
target-natural source-reconstruction chain recorded below.

### t02A03 closed after the point-wedge construction campaign

`t02A03` is **CLOSED** at `61f8ece4`.  Its initial torus bridge was banked at
`301501c2` and corrected to the declared product-multiplicative orientation at
`7ea2c595`.  The remaining dependency chain comprises:

- quotient/open-cover geometry: `7cfa9888`, `ac910fb4`, `8bc28a2d`,
  `c5b6f9cd`, `17d8e69e`, `f2394dd6`, and `0fc1cb8c`;
- actual-arrow Mayer--Vietoris: `31d0d05c`, with torus-first `Fin 3` repair
  `61e03da1`;
- generic span transport and actual wedge cells: `2e436010`, `ec9cc067`,
  `edc3e34a`, `a4165ca3`, `81261a1e`, `cfdcbd47`, and `1f4baec3`;
- point-span/free-product representation and target naturality: `672c9a83`,
  `908bb038`, `789791f9`, `006b106b`, `c2b33523`, `76cc892c`, `64c89ca6`,
  `e6db5c09`, and `7edd74c6`;
- connector coordinates and actual-span composition: `93744662`, `d4be08c8`,
  `401d4162`, and `16f3bb24`;
- target-natural mapping equivalence and source reconstruction: `65874214`,
  `68243152`, and `a178f80d`;
- generic relation-quotient transport: `f8cef535`.

Final fixture `/tmp/T02A03FullClosureProbe.lean` has SHA-256
`78fe0bb9cff9320106791b9137133c4c9b66300f2d9e8c8b535debf3dba8894e`.
Implementation job `invoke-1788293584627-7110-84f184fd` produced the exact
one-file closure; independent review `invoke-1788293762727-7114-8c51832a`
returned `PASS`.  The bridge-2 and final statement hashes remain
`4b6b72a8a93414fb7d7260166fff717cfc06c98b56f9c82ba77fea7e44556641`
and `923296b0aa0e70d9702cdd5d9767dffc54ce7e1c5ee4f2bda9d624321ee85624`.
Placeholders are `2 → 0` in the closing commit (`3 → 0` across the campaign),
the changed problem emits zero warnings, the full build passes, and both
closed theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

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
