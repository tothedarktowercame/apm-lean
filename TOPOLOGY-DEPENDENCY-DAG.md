# Topology dependency DAG

Date: 2026-08-27

This is the canonical topology roadmap.  It separates compiled mathematics,
consumer uptake, small remaining constructions, missing shared APIs, and
foundational library programs.  A `sorry` count alone does not determine a
node's state.

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
       └── MAYER-VIETORIS APPLICATIONS [API-GAP]

MANIFOLD-CALCULUS [BANKED MATHLIB SUBSTRATE]
       ├── PRODUCT-COMPLEMENT IMAGE NULLITY [BANKED]
       │      ├── ARBITRARY FINRANK ADAPTER [BANKED]
       │      └── ONE-CHART DIMENSION-DROP NULLITY [BANKED]
       │             └── COUNTABLE CHART RANGE DECOMPOSITION [BANKED]
       │                    ├── DIFFERENTIABLE-ON LOCAL NULLITY [LOCAL-GO]
       │                    ├── COMMON TARGET-CHART NULL TRANSPORT [API-GAP]
       │                    └── MANIFOLD-SARD [FOUNDATION]
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
       ├── QUOTIENT AND GLUING PI1 [FOUNDATION]
       ├── SURFACE CUTTING/CLASSIFICATION [FOUNDATION]
       └── INTERSECTION/SELF-INTERSECTION [depends on fundamental classes]
```

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

## Consolidation queues

### Queue A: canonical banking and uptake

The breadth-first survey produced several mathematically closed branches.
Each item must be checked against canonical master and independently reviewed
before it is marked `BANKED`:

- `t00J01`: exact Circle fibre cardinalities and regularity;
- `t03J06`: capped-cylinder integral and final conjunction;
- `t94J06`: degree-four disk zero obstruction;
- `t97J06`: Circle noncontractibility consumer;
- `t98A05`: exterior derivatives, simplex integral, circle-period obstruction,
  and final conjunction;
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

- sphere and ball moment calculations after a shared measure normalization;
- finite coordinate and derivative calculations already isolated in the leaf
  survey;
- range/subtype transports such as the middle-interval homeomorphism seam;
- problem-facing adapters for results already canonical and reviewed.

These tasks may be parallelized because their statements do not assume a
shared foundational conclusion.

### Queue D: foundational programs

Ranked by demonstrated reuse:

1. oriented-manifold fundamental classes and localization;
2. manifold Sard plus regular-preimage/submersion geometry;
3. manifold integration and Stokes;
4. covering classification and equivariant gluing;
5. Poincare/Thom/intersection comparison;
6. van Kampen and compact-surface foundations.

Each program requires a separate design note and a first milestone that
compiles independently of every final problem.

## Problem clusters

| Cluster | Representative consumers | Current disposition |
|---|---|---|
| Manifold Sard/nullity | `t01A08`, `t01J04`, `t92J07`, `t93A04`, `t94J05`, `t95J04`, `t96J05` | `FOUNDATION`; do not create problem-specific Sard assumptions |
| Regular/transverse preimages | `t00J02`, `t02A07`, `t94A06`, `t97J05` | `FOUNDATION`; begin with boundaryless regular-preimage geometry |
| Fundamental classes/localization | `t00J02`, `t00A01`, `t98A02`, `t00A04`, `t01A05` | `FOUNDATION`; highest-priority homological program |
| Intersection theory | `t00J02`, `t03J05`, `t93A05`, `t96J06` | depends on fundamental classes and cap/Thom comparison |
| Covering constructors | `t01A02`, `t01A04`, `t92J06`, `t98A01` | product is bounded; pullback next; gluing deferred |
| Circle degree/lifting | `t91A08`, `t94J06`, `t97A02`, `t97J08` | mixed concrete progress; shared naturality/lifting APIs remain |
| Sphere orientation/homology | `t02A08`, `t94J08`, `t95J04`, `t98A02` | computations exist; naturality under concrete maps remains |
| Stokes and moments | `t01J06`, `t02A05`, `t94A10`, `t95J05`, `t96J08` | shared measure/integration program plus bounded calculations |
| Surface classification/gluing | `t00A03`, `t01J01`, `t91J05`, `t94J09`, `t99J03` | late `FOUNDATION`; do not reduce recursively yet |

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

## Problems closed during consolidation

| Problem | Canonical closure | Audit result |
|---|---|---|
| `t01A03` | `8ef14798` | no executable placeholders; only standard axioms |
| `t01J02` | `3ba7726a` using `37524eb4` | status `solved`, zero placeholders, statements unchanged, only standard axioms |

## Next decision point

After the first Queue A promotion batch is independently reviewed, elect two
bounded program milestones:

1. extraction of the low-degree cap module;
2. a design/prototype for oriented-manifold local fundamental classes.

Continue chartwise Sard work only at the Euclidean dimension-drop nullity
interface.  Do not begin a monolithic manifold-Sard implementation until that
prototype and the regular-preimage interface have been separately reviewed.
