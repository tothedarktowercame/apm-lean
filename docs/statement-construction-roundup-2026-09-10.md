# APM statement-construction roundup — 2026-09-10

Historical initial roundup. The subsequent [implementation report](statement-encoding-progress-2026-09-10.md)
records twelve compiled statements; the adjacent JSON now includes that progress.

The 491/460 discrepancy is real, but it is not evidence that 31 problems are
inexpressible in Lean. The remaining set comprises **28 topology problems, two
LTS statements, and one incomplete analysis source**. Missing definitions should
become explicit construction work. Several old skip reasons mistakenly require
proof theorems before allowing the corresponding statements to be written.

This document specifies that work for every missing problem. The adjacent
[JSON backlog](statement-construction-backlog-2026-09-10.json) records all 31 source
hashes, proposed construction packages, reuse candidates and source-review issues.
These are construction specifications, not newly compiled Lean declarations.

## Reproduced census and its limits

The source universe is `apm/*.tex`, exactly as in
[the report scanner](/home/joe/code/futon0/contrib/stack-hud.el:2142).
A bundle counts as Lean material if **any** `.lean` file exists recursively under
`problems/ID/lean/`. Candidates and historical files do not count.
An informal solution counts when its file is at least 100 bytes.

| Measured category | Count |
|---|---:|
| Canonical source stems | 491 |
| Informal files meeting the size threshold | 491 |
| Canonical bundles with current Lean material | 460 |
| Canonical bundles with none | 31 |
| Other, non-source-stem bundles with Lean (BPM) | 10 |

491 informal files does not mean 491 completed or correct informal proofs:
`a98J05` explicitly records a missing conclusion; other files flag ambiguities.
Likewise 460 is a material-presence count, not full statement coverage or proof
certification. No report metric or problem status was changed in this roundup.

## Earlier work recovered

- The [September 7 skip log](statement-encoding-skips-2026-09-07.md) records
  codex-2/claude-3's first tranche and a second tranche: 36 listed IDs in total.
- The September 8 corrections by claude-5 acknowledge that proof machinery is
  not required merely to state a classification. `tunk01` constructs quotient
  spaces and states a homeomorphism; it does not first prove surface classification.
- Six originally skipped bundles gained material: `t99A01`–`t99A05` and `tunk01`.
  `t99A05` was then withdrawn in `d63e60d6` on Joe's ruling against dropped
  hypotheses. Thus **36 - 6 + 1 = 31**, exactly today's missing set.
- `f3ce843e` landed partial encodings for `t99A01`–`t99A05`.
  `d63e60d6` added dropped-structure screening and removed `t99A05/Main.lean`.
  These are concrete history anchors; the correction note's referenced
  `bcdab261` should not be treated as the sole implementation commit.
- `scripts/check_statement_quality.py --all-missing` recognizes old skips and
  asks the next investigator to read their reasons. It creates no definition
  targets and does not reconsider their mathematical premises. This explains
  how a remembered skip can persist; it is not evidence that nothing else was
  attempted by other agents.

The old note's 471 encoded bundles uses a different denominator: with the ten
BPM bundles and the then-present `t99A05`, 460 + 10 + 1 = 471. Today's full
bundle-tree material count is 470. Keep source-stem scope explicit.

## What has already been constructed

The pinned Mathlib revision is recorded in the JSON. This is a local source
inspection, not a claim about the latest upstream release or a fresh compilation.

- `ConstructionTargets/Surfaces.lean` defines polygon quotients with coinduced
  topology. Its Euler-characteristic function is on classification **data**;
  it is not yet the homological Euler characteristic of arbitrary manifolds.
- `PointWedgeQuotient.lean` constructs actual point wedges and quotient
  comparisons. `CoveringDegree.lean` defines `IsKSheetedCover` using actual
  covering maps, finite fibers and their cardinalities. `CircleUniversalCover`
  supplies the real-line circle cover.
- `ManifoldRegularFiberGlobalAtlas`, its tangent-image companion, and the
  manifold-target/incidence modules contain actual chart and derivative work.
  This is a stronger starting point than the old blanket regular-value skip.
- `Intersection.lean` supplies finite signed sums from oriented linear data.
  Its own documentation says the connection to embedded submanifold tangents
  remains geometric work. `OrientedSurfacePreimageDuality` explicitly describes
  a still-required producer; an interface is not a completed theorem.
- Pinned Mathlib has Euclidean differential forms, exterior derivative and
  pullback; `OrientedIntegration.lean` adds orientation-sensitive coefficient
  integration. Neither alone supplies arbitrary manifold forms and intrinsic
  integration. Capped-cylinder integral modules are reusable parameter-integral
  work for `t03J06`, not solutions to `t93J05`'s different printed geometry.
- `SingularHomologyConcrete.lean` already defines integral singular homology.
  Building a homological invariant is not starting from an empty repository.
- Mathlib's `Measure/GiryMonad.lean` exists. Whether it models the particular
  LTS monad is a source-definition question, not settled by the shared word monad.

## Construction packages

Package names below are proposed backlog IDs, not claims that new Lean modules
have been installed. A problem can consume several packages; there are 31
problems, not necessarily 31 distinct missing concepts.

### spaces-covers — Concrete spaces, attachments and covers

**Definition target.** Quotient topology for polygon surfaces, antipodal spaces, wedges and cell attachments; actual continuous quotient maps; based loops and induced fundamental-group maps; IsKSheetedCover and simply connected covering total spaces.

**Remaining obligations.** Connect models by homeomorphisms/homotopy equivalences at the appropriate strength. Prove smooth/manifold certificates only where demanded. Surface classification, subgroup classification, van Kampen and cover computations may remain open theorem targets.

**Consumers (10).** `t00J05`, `t93J03`, `t95A01`, `t96A01`, `t96A02`, `t96J02`, `t98J02`, `t98J05`, `t99J01`, `t99J02`

### smooth-quotients — Smooth projective and quotient geometry

**Definition target.** Construct RP^n/CP^n and torus quotient topologies, representative-independent maps and coordinate charts. Where smoothness is demanded, build ChartedSpace/IsManifold instances and actual tangent maps.

**Remaining obligations.** Chart transitions and quotient/local-chart compatibility are construction obligations. A bare type named RP2 or an arbitrary smooth-space parameter is not a realization of this target.

**Consumers (8).** `t93A05`, `t93A06`, `t95A01`, `t95A04`, `t96A06`, `t96A07`, `t98J05`, `t99J05`

### regular-geometry — Regular values, submanifolds and vector fields

**Definition target.** CriticalValues(f) = f image {x | not Surjective(mfderiv f x)}; submersion = smooth plus pointwise derivative surjectivity; embedded submanifolds with dimension and tangent inclusion; transversality by spanning tangent ranges; smooth tangent sections and induced fiber manifolds.

**Remaining obligations.** Reuse existing fiber-atlas/tangent constructions after checking exact typeclass requirements. No need to finish Sard, flow completeness or all regular-value theorems before expressing the desired propositions. Boundary/orientation data must be geometric, not arbitrary flags.

**Consumers (9).** `t95A05`, `t96A07`, `t97A05`, `t97A06`, `t97A07`, `t98A06`, `t98J06`, `t99A05`, `t99A06`

### forms — Manifold forms, exterior derivative and oriented integrals

**Definition target.** Smooth alternating covector fields with chart transformation law; actual derivative pullback and exterior derivative; closed/exact predicates; integration of top forms and parameterized curves/surfaces with fixed orientations. For torus descent use periodic coefficients plus explicit equivalence to quotient-manifold forms.

**Remaining obligations.** Existing Euclidean DifferentialForm and signed coefficient integrals are starting points. Chart independence, quotient compatibility, boundary orientation and geometric meaning of parameter integration are construction obligations. Stokes, extension and final integral computations are theorem targets, not arbitrary assumed operators.

**Consumers (6).** `t93A06`, `t93J05`, `t95A05`, `t97A06`, `t98J05`, `t99J06`

### intersection — Geometric degree and intersection

**Definition target.** Tie incidence points and derivative tangent-sum maps of actual embeddings to Intersection.PointDatum; define signed finite sums and parity, local graph/diagonal signs, and degree for its supported compact/proper domain.

**Remaining obligations.** Derive finiteness and independence of frames/regular value/perturbation where needed. Existing Intersection is linear algebra; OrientedSurfacePreimageDuality documents an unfilled producer interface. Neither alone supplies a completed manifold intersection invariant.

**Consumers (5).** `t93A05`, `t97A05`, `t98J06`, `t99A05`, `t99J05`

### homological-invariants — Homological Euler characteristic and Lefschetz number

**Definition target.** Construct rational homology of the named spaces and induced maps; package finite dimensionality and vanishing above a bound; define chi as alternating dimensions and L(f) as alternating traces. Connect local fixed-point indices to actual charts.

**Remaining obligations.** Integral singular homology already exists locally; inspect coefficient infrastructure for a rational model. Finiteness certificates and bound independence are construction obligations. Kunneth, fixed-point formulas and values such as chi(CP^n)=n+1 remain proof targets. Never define the invariant to equal the desired answer.

**Consumers (5).** `t96A06`, `t98J01`, `t99A06`, `t99J02`, `t99J05`

### knots — Concrete links and embedded disks

**Definition target.** Explicit embedded circles in R3, complement loops, solid torus S1 x D2 and its cover R x D2; disk-bounding by a topological/smooth embedding with prescribed boundary; linking as a degree or intersection invariant if needed.

**Remaining obligations.** Recover the missing t98J04(b) picture before selecting its embedding. General knot classification is not necessary just to state null-homotopy or embedded-disk nonexistence.

**Consumers (1).** `t98J04`

### borel-spectra — Source-faithful Borel spectrum model

**Definition target.** Source-defined spectra, equivariant/Borel objects, equivalences and restriction. A chosen concrete model must match the source homotopy theory; record its comparison to Fun(BG,Sp) if that is the route.

**Remaining obligations.** An abstract theorem that evaluation reflects isomorphisms can be supporting work, but cannot count as the spectral statement until the model/comparison is supplied.

**Consumers (1).** `lts-derived-induction-lem3`

### pettis-monad — Source measure monad and Pettis barycenters

**Definition target.** Recover exact source M, then define its objects, morphisms, unit, multiplication and measure bounds; define weak sigma algebra, norm bornology and Pettis barycenter by all continuous linear functionals; state c(unit x)=x and c(M c Xi)=c(join Xi).

**Remaining obligations.** Mathlib has a Giry monad, but that does not identify this source monad. Measurability, bornological boundedness, Pettis existence/uniqueness and the unit/multiplication construction obligations must be explicit; do not assume the final algebra laws as input.

**Consumers (1).** `lts-monadic-integration`

## All 31 problem targets

The targets below describe the required complete statements; numeric answers
quoted from informal solutions still require fidelity review, not just typechecking.

### a98J05

[Printed source](../apm/a98J05.tex) · [Informal analysis](../problems/a98J05/informal-solution.md)

**Construction:** Recover the missing conclusion before choosing any construction target.

**Review:** The TeX ends after the analytic power-series assumption. The informal file explicitly says there is no problem to solve.

**Packages:** source recovery first.

### lts-derived-induction-lem3

[Printed source](../apm/lts-derived-induction-lem3.tex) · [Informal analysis](../problems/lts-derived-induction-lem3/informal-solution.md)

**Construction:** Specify the intended category of Borel-equivariant spectra, restriction to e, and detection of equivalences for its morphisms.

**Review:** Recover source definitions: genuine spectra restricted to Borel objects versus Fun(BG,Sp), and the comparison between these models. Ordinary equivariant objects alone do not formalize spectra.

**Packages:** borel-spectra.

### lts-monadic-integration

[Printed source](../apm/lts-monadic-integration.tex) · [Informal analysis](../problems/lts-monadic-integration/informal-solution.md)

**Construction:** Specify the source measure monad on bornological measurable spaces, the weak measurable structure and norm bornology of X, Pettis barycenter, and the two algebra laws.

**Review:** The stem never defines M or enough Pettis integrals. Recover measure class, support/variation bounds and morphisms; do not substitute the Giry monad by assumption.

**Packages:** pettis-monad.

### t00J05

[Printed source](../apm/t00J05.tex) · [Informal analysis](../problems/t00J05/informal-solution.md)

**Construction:** Define the torus with a disk attached along the given essential embedded circle, an actual simply connected covering model, and continuous maps S2 -> X and X -> S2 that are not null-homotopic.

**Review:** The informal solution moves through X homotopy-equivalent to S1 wedge S2. That does not by itself identify the original universal cover homeomorphically; preserve the requested geometric covering description.

**Packages:** spaces-covers.

### t93A05

[Printed source](../apm/t93A05.tex) · [Informal analysis](../problems/t93A05/informal-solution.md)

**Construction:** State all three parts: null-homotopy of smooth S2 -> RP3; existence of compact circle/surface submanifolds with odd mod-2 intersection; nonexistence for oriented nonzero integral intersection.

**Review:** Preserve compactness, dimensions, embeddings, and orientation in the respective parts; clarify transverse representatives in the definition of intersection.

**Packages:** smooth-quotients, intersection.

### t93A06

[Printed source](../apm/t93A06.tex) · [Informal analysis](../problems/t93A06/informal-solution.md)

**Construction:** Define torus forms, projection pullback, integral and exterior derivative; state unique descent of the printed form, integral 1/4, a Euclidean primitive, no torus primitive, and the specified parallelogram period.

**Review:** Use the actual quotient R2/Z2 and all three source parts. Stokes and descent theorems are later proof work.

**Packages:** smooth-quotients, forms.

### t93J03

[Printed source](../apm/t93J03.tex) · [Informal analysis](../problems/t93J03/informal-solution.md)

**Construction:** Define a concrete Klein bottle and chosen based generator loops; state its fundamental-group presentation and the plane embedding of each subspace satisfying the printed inclusion-image condition.

**Review:** Retain path connected, locally path connected and semilocally simply connected; bind the subgroup generator to the actual loop through the presentation map.

**Packages:** spaces-covers.

### t93J05

[Printed source](../apm/t93J05.tex) · [Informal analysis](../problems/t93J05/informal-solution.md)

**Construction:** Define the printed alternating 2-form and its derivative; define oriented integration on the exact printed surface once its geometry is resolved.

**Review:** The cylinder x^2+y^2=1 has no z bounds and no bottom cap. The informal solution calls it a closed bounding surface and returns zero. This is a source/solution conflict, not an absent-API verdict.

**Packages:** forms.

### t95A01

[Printed source](../apm/t95A01.tex) · [Informal analysis](../problems/t95A01/informal-solution.md)

**Construction:** State the three existence/nonexistence questions for actual spaces, connected double coverings, nonorientable surfaces and finite fundamental groups.

**Review:** A group presentation is supporting material only; the self-cover must be a map from the same surface to itself. Do not add niceness assumptions to the universal nonexistence claim merely to use classification.

**Packages:** spaces-covers, smooth-quotients.

### t95A04

[Printed source](../apm/t95A04.tex) · [Informal analysis](../problems/t95A04/informal-solution.md)

**Construction:** Construct RP2 as the antipodal sphere quotient with a smooth atlas; define the six-coordinate descended map and state smooth embedding onto its submanifold image.

**Review:** A polynomial identity upstairs or topological injection alone omits the conclusion.

**Packages:** smooth-quotients.

### t95A05

[Printed source](../apm/t95A05.tex) · [Informal analysis](../problems/t95A05/informal-solution.md)

**Construction:** Define oriented embedded manifolds with boundary, boundary orientation, separation of A and B, and integration of closed forms; state separator existence, independence of its integral, and finiteness of nondegenerate fixed points.

**Review:** Part (c) defines Lefschetz fixed point by invertibility of df-id; it does not require a global Lefschetz number or theorem to state it. Specify the separator boundary avoids A and B so the integral has its declared domain.

**Packages:** regular-geometry, forms.

### t96A01

[Printed source](../apm/t96A01.tex) · [Informal analysis](../problems/t96A01/informal-solution.md)

**Construction:** For an actual closed orientable genus-four surface and H <= pi1(S) of finite index n, state an isomorphism to the surface presentation with genus 3*n+1.

**Review:** Reidemeister-Schreier and surface-cover classification prove the statement; they are not needed before stating the group isomorphism.

**Packages:** spaces-covers.

### t96A02

[Printed source](../apm/t96A02.tex) · [Informal analysis](../problems/t96A02/informal-solution.md)

**Construction:** Construct RP2 wedge RP2 as a topological quotient and state: every continuous self-map has a fixed point.

**Review:** No Lefschetz number or fixed-point theorem is needed to WRITE this assertion. Concrete quotient geometry is the statement requirement.

**Packages:** spaces-covers.

### t96A06

[Printed source](../apm/t96A06.tex) · [Informal analysis](../problems/t96A06/informal-solution.md)

**Construction:** Define real projective 3-space and the descended quadratic map, its homological Lefschetz number, and the assertion that it is not homotopic to identity.

**Review:** Only topological quotient/continuity is demanded in this problem; a smooth quotient atlas is not a prerequisite for these parts. Do not identify Lefschetz number with a guessed numeric constant.

**Packages:** smooth-quotients, homological-invariants.

### t96A07

[Printed source](../apm/t96A07.tex) · [Informal analysis](../problems/t96A07/informal-solution.md)

**Construction:** Define the antipodal quotient and descended map (yz,xz,xy); express transversality through actual tangent maps to the axis/planes and state the infinitely-many intersecting transverse planes assertion.

**Review:** Part (b) concerns the descended map; part (c) names the original map. Retain this distinction.

**Packages:** smooth-quotients, regular-geometry.

### t96J02

[Printed source](../apm/t96J02.tex) · [Informal analysis](../problems/t96J02/informal-solution.md)

**Construction:** Bind G to pi1 of the concrete Klein bottle and state every finite-index subgroup is isomorphic to either that Klein-bottle group or Z x Z, with realizations.

**Review:** The classification theorem belongs in the proof; a presented group without its connection to the space is only a partial encoding.

**Packages:** spaces-covers.

### t97A05

[Printed source](../apm/t97A05.tex) · [Informal analysis](../problems/t97A05/informal-solution.md)

**Construction:** Define the geometric integer intersection pairing for the actual embedded W and Z; retain all dimensions, orientations, compactness, no-boundary and connectedness conditions; conclude connectedness of Y minus W.

**Review:** A finite signed sum without its connection to these submanifolds is insufficient; invariance under transverse perturbation is needed if the source does not assume transversality.

**Packages:** intersection, regular-geometry.

### t97A06

[Printed source](../apm/t97A06.tex) · [Informal analysis](../problems/t97A06/informal-solution.md)

**Construction:** Define manifold forms, pullback along an embedded inclusion, a positive top-degree volume form, and closedness; state extension and nonclosedness of extensions when inclusion is null-homotopic.

**Review:** Preserve positive dimension, nonempty compact oriented smooth X and its embedding. Tubular-neighborhood/Stokes proofs can remain open.

**Packages:** forms, regular-geometry.

### t97A07

[Printed source](../apm/t97A07.tex) · [Informal analysis](../problems/t97A07/informal-solution.md)

**Construction:** Define critical values as the image of points where mfderiv is not surjective; state nonempty compactness and infinitude for n>1 and a nonconstant smooth map.

**Review:** Part (a) fails at n=0. Resolve the source convention for R^n before adding n>0; no full Sard theorem is needed to define this set.

**Packages:** regular-geometry.

### t98A06

[Printed source](../apm/t98A06.tex) · [Informal analysis](../problems/t98A06/informal-solution.md)

**Construction:** Define smooth tangent-bundle sections, derivative-surjectivity submersion, vector-field lift equation, and a diffeomorphism of the two regular fibers with their induced manifold structures.

**Review:** Flow completeness and partition-of-unity lifting are proof methods, not prerequisites for writing the two assertions.

**Packages:** regular-geometry.

### t98J01

[Printed source](../apm/t98J01.tex) · [Informal analysis](../problems/t98J01/informal-solution.md)

**Construction:** Define the explicit product map on S2 x S1 x S1; define Lefschetz number from induced finite-dimensional rational homology maps; state value 8 and that this map is not homotopic to the identity.

**Review:** Retain the precise comparison with the identity. Kunneth is a later computation proof.

**Packages:** homological-invariants.

### t98J02

[Printed source](../apm/t98J02.tex) · [Informal analysis](../problems/t98J02/informal-solution.md)

**Construction:** For closed surfaces and a finite cover, define simple closed curves as embedded circles, the specified degree-one lift, and separation by disconnected complement; state (a) and a counterexample to (b).

**Review:** Define closed surface with its actual manifold and compactness conditions. Homology and surface-separation classification are possible proof tools, not requirements for the statement.

**Packages:** spaces-covers.

### t98J04

[Printed source](../apm/t98J04.tex) · [Informal analysis](../problems/t98J04/informal-solution.md)

**Construction:** Construct explicit linked circles for (a), their complement and loop; define a solid torus and disk-bounding as an embedded disk with the given boundary for (b).

**Review:** The informal file identifies an absent diagram/parametrization for (b). Obtain that specification; do not select an arbitrary knot from the verbal description.

**Packages:** knots.

### t98J05

[Printed source](../apm/t98J05.tex) · [Informal analysis](../problems/t98J05/informal-solution.md)

**Construction:** Specify the genus-two embedded surface, half-turn action and quotient torus, covering coordinates, descended alpha and beta; state closed/not-exact and a non-null-homotopic loop with zero period.

**Review:** The printed x~y iff y=T(x) is not reflexive away from fixed points. Record the intended orbit-generated equivalence explicitly; also specify the geometric action and branched quotient rather than pretending it is everywhere a cover.

**Packages:** smooth-quotients, forms, spaces-covers.

### t98J06

[Printed source](../apm/t98J06.tex) · [Informal analysis](../problems/t98J06/informal-solution.md)

**Construction:** Define graph/diagonal manifold transversality and the oriented local intersection at a fixed point; state invertibility of df-id and its orientation sign.

**Review:** Connect the existing signed linear intersection datum to actual tangent inclusions, and fix order/normal orientation (b-a) explicitly. Do not stop at the linear-algebra half.

**Packages:** regular-geometry, intersection.

### t99A05

[Printed source](../apm/t99A05.tex) · [Informal analysis](../problems/t99A05/informal-solution.md)

**Construction:** Define mod-2 degree with its legitimate domain and mod-2 intersection of actual smooth submanifolds; retain dim Z=dim Y and the existential COMPACT W.

**Review:** Withdrawn encoding fixed W to a fiber and erased hypotheses. The current informal yes proof also needs compactness/properness not printed for X/f. Resolve the literal question (including possible counterexample) before selecting a yes theorem.

**Packages:** intersection, regular-geometry.

### t99A06

[Printed source](../apm/t99A06.tex) · [Informal analysis](../problems/t99A06/informal-solution.md)

**Construction:** Define Euler characteristic from actual homology and submersion to the circle; state the obstruction under the verified source manifold convention.

**Review:** The informal proof adds compactness and no boundary. Recover the convention or record a corrected source separately; do not silently strengthen the printed hypothesis.

**Packages:** homological-invariants, regular-geometry.

### t99J01

[Printed source](../apm/t99J01.tex) · [Informal analysis](../problems/t99J01/informal-solution.md)

**Construction:** Construct a wedge of three circles and finite-sheeted covers; state existence for every positive degree and the connected-cover group F_(2*n+1), with the disconnected componentwise alternative.

**Review:** The source does not say covers are connected. Preserve the distinction rather than forcing all covers to have one basepoint-independent fundamental group.

**Packages:** spaces-covers.

### t99J02

[Printed source](../apm/t99J02.tex) · [Informal analysis](../problems/t99J02/informal-solution.md)

**Construction:** Construct the double-torus CW and connected-sum models and their comparison; state the actual space homology groups and fundamental-group presentation, with maps/complexes for the requested two calculation methods.

**Review:** Bare ranks and three abstract propositions were among the reverted pseudo-statements. van Kampen/Mayer-Vietoris can be open proof dependencies; actual chain maps and spaces must be identified.

**Packages:** spaces-covers, homological-invariants.

### t99J05

[Printed source](../apm/t99J05.tex) · [Informal analysis](../problems/t99J05/informal-solution.md)

**Construction:** Construct topological/smooth CP^n and its coordinate charts, diagonal projective map and homotopy; define local fixed-point index and Euler characteristic; state all five parts, including chi(CP^n)=n+1.

**Review:** Use real orientation of complex charts; local fixed-point sign uses id-df, distinguish it from the graph convention in t98J06.

**Packages:** smooth-quotients, homological-invariants, intersection.

### t99J06

[Printed source](../apm/t99J06.tex) · [Informal analysis](../problems/t99J06/informal-solution.md)

**Construction:** Define the literal alternating 2-form, exterior derivative and parameterized oriented cone integral; state d alpha=(2z+1) dx wedge dy wedge dz and integral 9*pi/2.

**Review:** Retain dz wedge dz=0 exactly as printed. Record a suspected typo separately; handle the singular apex through the parameterized surface/chain definition, not a global smooth-surface assumption.

**Packages:** forms.

## First statement-writing tranches

1. **Concrete topology with existing quotient/cover vocabulary:** `t96A02`,
   `t98J02`, `t96A01`, `t96J02`, `t99J01`. The smallest first candidate is
   `t96A02`: construct the two projective planes and their wedge, then quantify
   over continuous self-maps and fixed points. It requires no Lefschetz
   definition to state. A proof may use Lefschetz much later.
2. **Derivative-defined geometry:** `t97A07` after resolving n>0,
   `t98J06` after connecting tangent inclusions to the local-sign definition,
   and `t98A06` using actual induced fiber atlases. Treat vector-field/flow
   existence as later proof work.
3. **Shared quotient smoothness and forms:** build the precise smooth/projective
   objects for `t95A04`/`t96A07`, and the form/integration definitions consumed
   by `t93A06`/`t97A06`/`t99J06`. The cone is a useful explicit parameterized
   integration consumer; it does not require a smooth structure at its apex.
4. **Global invariants and larger geometry:** finish the definitions and
   finiteness certificates needed for `t93A05`, `t97A05`, `t98J01`, `t99J02`,
   `t99J05`, and the remaining multi-part problems. Keep proof producers as
   separately named obligations rather than parameters hiding the conclusion.
5. **Source recovery alongside construction work:** `a98J05`, the LTS source
   definitions, `t93J05`, `t98J04(b)`, and the recorded source conventions.
   Generic construction work may proceed, but source-dependent final statements
   remain pending. In particular, failed compactness in one proposed proof of
   `t99A05` is not itself a proof that the literal question has a negative answer.

## Acceptance criteria for subsequent implementation

For each target, record the source clause, the concrete object/operation that
expresses it, and the separately open proof obligation. New construction
records should have states such as specified, defined, well-definedness-open,
realized, and consumer-statement-reviewed. A target with open construction
certificates must not be advertised as a realized reusable construction.

Definitions must describe the geometry or algebra independently of the wanted
answer. Do not use free `Prop` parameters, opaque invariants with no construction,
assume the theorem as a structure field, substitute arbitrary scalar functions
for forms, or drop smoothness, dimensions, orientations or source parts.
A `sorry` on the final theorem distinguishes an unproved statement from a proof;
it does not make a fabricated definition or an unrealized structure sound.

Before counting a **complete statement**, map every source part and hypothesis
to the actual Lean declaration and its imports. Compile and run the existing
statement-quality screen when implementing, then independently review the
mathematical fidelity: the screen is explicitly heuristic and has passed
incomplete encodings before. Test elementary non-vacuity and representation
compatibility of new definitions where meaningful. No full problem proof is
required for this milestone.

Do not merge this milestone into the existing material counter. A useful future
report would show material present, complete statement reviewed, and construction
requirements still open as separate quantities, derived from per-part evidence.
`t99A01`–`t99A04` are immediate candidates for that separate coverage audit:
their current file headers explicitly omit source geometry or entire parts,
although all four count among the 460. They were inspected here but not changed.

## Validation of this roundup

Recomputed the source-stem census using the same file-presence and informal-size
rules as the report. Verified all 31 missing IDs are exactly the historical skip
set minus the five currently encoded survivors. Checked every referenced local
starting-point path and source hash in the machine-readable backlog. Read every
missing source and inspected the associated informal analyses (focused review,
not a proof audit). No Lean files, shared JVMs, source statements, or existing statuses were
modified; no Lean compilation or proof certification is claimed.
