# Topology closure experiments

Date: 2026-08-30

Status: process note for the topology portfolio

## Purpose

The topology program has accumulated substantial reusable mathematics, but a
long sequence of compiled construction targets can advance without changing a
frozen problem.  This note defines how we choose the next theorem to prove.

The governing question is not “what foundational theorem would be useful?”
It is:

> Which single absent reusable theorem is demonstrably on the shortest current
> route from canonical master to a named frozen placeholder?

`TOPOLOGY-DEPENDENCY-DAG.md` records the mathematical state.  This note records
the process used to change that state.

## Evidence behind the change

`futon3c/holes/technotes/TN-fable-F36-F57-review.md` studied recent non-topology
APM frames and memory use.  Its transferable observations are limited but
useful:

- the solver closed most problems it was actually given;
- several first attempts closed with no used memories;
- the clearest cross-problem memory use mainly confirmed an API route already
  suggested by the consumer;
- process memories may affect route choice even when token fingerprints cannot
  certify that effect;
- same-problem deposits were more visibly connected to later proof artifacts
  than distant analogies.

These facts do not imply that topology problems should copy methods from those
frames.  They suggest that retrieval is best used to nominate a route or locate
an API, while a consumer-facing compile test decides whether the route fits.

## Unit of work

The scheduling unit is a **closure experiment**, not an open-ended foundational
program.

Each experiment has exactly one frozen consumer and at most one candidate
missing theorem.  It proceeds as follows:

1. Select one executable placeholder in a frozen `Main.lean`.
2. State the shortest plausible route using declarations on canonical master.
3. Record any memory, analogy, or prior construction that suggested the route.
   This is provenance, not proof evidence.
4. Build a small fixture which imports canonical modules and reaches the
   candidate theorem's actual input and output types.
5. Do not assume the candidate theorem.  The fixture must stop at a typed hole,
   a failed `exact`, or a separately stated proposition.
6. Report the exact residual after the candidate theorem: either the frozen
   placeholder closes, a bounded final adapter remains, or the route does not
   fit.
7. Elect implementation only when the experiment identifies one reusable
   theorem with at least two named consumers and a bounded final adapter for
   the first consumer.

An experiment is allowed to conclude that no useful theorem should be built.
That is a successful scheduling result.

## Required report

Every closure experiment reports these fields:

```text
consumer:
frozen placeholder:
recalled suggestion:
canonical declarations reached:
representation at the seam:
candidate missing theorem:
other named consumers:
residual after the theorem:
compile evidence:
decision: ELECT | REVISE | STOP
stop reason:
```

“This resembles theorem X” belongs under `recalled suggestion`.  It does not
belong under `canonical declarations reached` unless the declaration has been
inspected and typechecked in the fixture.

## Stop rules

Stop an experiment or implementation chain when any of the following occurs:

- two successive packets add infrastructure without reducing the named
  consumer residual;
- the route needs two independent absent foundational theorems;
- the frozen hypotheses do not supply a structure the route requires;
- a fixed-target equivalence is being used as a source equivalence without a
  natural representability theorem;
- a concrete coordinate construction is being renamed as a generic theorem;
- the proposed theorem has only the original consumer;
- progress consists only of another transport or associativity lemma and the
  consumer-facing fixture has not changed.

When a stop rule fires, preserve compiled work, classify the node accurately,
and return to the portfolio.  Do not weaken an invariant or add a conditional
producer to keep the route moving.

## Portfolio policy

Work is selected in this order:

1. selective uptake of compiled experimental closures;
2. frozen-facing adapters for canonical theorems;
3. one-edge experiments for `LOCAL-GO` and `API-GAP` nodes;
4. foundational programs supported by a successful experiment and at least two
   named consumers;
5. representation-specific development only while it shortens its named
   frozen consumer in the same bounded packet.

Mathematical importance alone does not elect a foundational program.  If no
experiment leaves one theorem and a bounded adapter, the portfolio returns to
uptake and local closures.

## Agency workflow

Portfolio work is visible and interruptible through Agency.

- Dispatch independent experiments with typed request bells.  Each bell names
  one consumer, one output report, and the stop rule.
- Do not ask several agents to edit the canonical DAG concurrently.  They
  return evidence; the portfolio owner updates the DAG once.
- Park the owner turn on the dispatched job ids.  The continuation resumes when
  the reports arrive, so synthesis is not dependent on the operator prompting
  the owner again.
- If an experiment discovers a prerequisite owned by another active job, park
  it on that concrete job id rather than polling or duplicating the work.
- Use a whistle only to reconcile a crossed or ambiguous bell.  Do not start a
  second implementation while the ownership of the first is unclear.
- A resumed owner either elects one implementation, requests a revised probe,
  or records `STOP`.  It does not automatically dispatch the next theorem in
  the same deep chain.

The owner commits process notes and DAG changes.  Experiment agents should be
read-only unless explicitly authorized to create a fixture or report in a
distinct owned file.

## Initial portfolio

The first run contains four experiments:

1. **Uptake audit.** Re-evaluate the six experimental closures in Queue A and
   nominate the smallest statement-preserving promotion.
2. **`t01J03` representability.** State the exact theorem converting the
   target-natural mapping equivalence into the chosen-basepoint automorphism
   group isomorphism required by `apm_t01J03_bridge_2`.
3. **`t95J04` product homology.** Determine whether the first missing edge is
   singular Eilenberg--Zilber, integral Kunneth, or coefficient transport.
4. **`t03J02` collar hypotheses.** Decide whether the frozen data actually
   supplies a collar or cofibration sufficient for an honest two-open cover.

After these reports, elect at most one implementation program.  The initial
ranking favors uptake because it has the shortest path to whole-problem
closure, but evidence from the probes may change the order.

## Initial portfolio results

The four probes ran through Agency and resumed through one parked join:

| Job | Consumer | Decision | Evidence-backed result |
|---|---|---|---|
| `invoke-1788087056758-3734-30eea7ea` | Queue A uptake | `CLOSED` after election | selectively promoted only `CircleNoncontractible.{lean,md}` from historical commit `2343da9e`; implementation `0ea00fce` closes the sole remaining `t97J06` placeholder by one specialization |
| `invoke-1788087059249-3735-3a33e65a` | `t01J03` | `STOP` | the complete fixed-target mapping equivalence is not yet target-natural at the generic pseudococone layer, so the proposed representability theorem cannot yet be instantiated |
| `invoke-1788087061996-3736-5773a9b6` | `t95J04` | `STOP` for foundations; local adapter available | the first product edge is singular Eilenberg--Zilber, followed independently by integral Kunneth; coefficient comparison is already banked; a retract argument can close the two clauses comparing `S⁶` with products without either foundation |
| `invoke-1788087064433-3737-7857d6c2` | `t03J02` | `STOP` | `IsEmbedding` plus `Nullhomotopic` supplies no collar/NDR neighbourhood; Jordan--Schoenflies and van Kampen are two independent absent foundations |

The elected implementation was the `t97J06` uptake, not a new foundational
program.  Its bounded packet was:

1. copy only `ConstructionTargets/CircleNoncontractible.lean` and its note from
   historical commit `2343da9e`;
2. independently audit the generic theorem against canonical
   `CircleSingularHomology`;
3. import it in frozen `t97J06` and discharge `apm_t97j06` with
   `t97J06_not_homotopic_const_of_not_contractibleCircle
   CircleNoncontractible.circle_not_contractible`;
4. compile the frozen problem with zero placeholders and record the closing
   commit in the DAG.

The `t95J04` retract adapter was the next local candidate after this election.
It received its own frozen-facing election, implementation, and independent
review, recorded below.

### Elected closure outcome

Implementation Agency job `invoke-1788087615270-3747-34cc93a0` committed the
scoped closure as `0ea00fcef70b21c9b653a4c11db959600680bcc4`.
Independent review job `invoke-1788087816801-3748-17bef30b` returned `PASS`:

- the Lean target is byte-identical to the selected historical source;
- the generic theorem imports no problem-specific adapter or conclusion;
- the frozen statement is unchanged and its placeholder count is `1 → 0`;
- direct target and frozen compilation passed;
- the focused build passed with 8,254 jobs;
- principal declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`;
- placeholder and diff audits are clean.

The final experiment decision is `CLOSED`.  This is the first application of
the process: four probes, three evidence-backed stops, one bounded election,
and one whole frozen problem closed before another foundational chain began.

### Bounded `t95J04` follow-up

Election job `invoke-1788088998881-3750-c29c22f9` independently compiled the
split-retract argument and returned `ELECT`.  The elected packet deliberately
excluded singular Eilenberg--Zilber, integral Kunneth, Sard, and the comparison
of `S² × S⁴` with `S³ × S³`.

Implementation job `invoke-1788089170654-3751-711e3944` committed
`54fe611541f8568e78ad222d84318f76892023dc`.  It adds the generic
`SingularHomologyRetractNonvanishing` target and uses it to supply exactly two
conjuncts of frozen `apm_t95j04`:

- `S⁶` is not homeomorphic to `S² × S⁴`;
- `S⁶` is not homeomorphic to `S³ × S³`.

Independent review job `invoke-1788089485653-3752-a094d808` returned `PASS`.
The frozen statement is unchanged and its placeholder count remains `1 → 1`,
but the surviving placeholder now covers only the Sard clause, the three
simple-connectivity clauses, and `S² × S⁴ ≄ S³ × S³`.  Direct target and frozen
compilation, the 8,253-job focused build, axiom audit, placeholder audit, and
diff check all passed.

The decision is **bounded partial closure**, not `CLOSED`: two named conjuncts
are compiled, while `t95J04` remains open and the stopped product-foundation
program remains stopped.

## Second portfolio round

The second round audited three historical uptake claims as consumer closures:

| Job | Consumer | Decision | Evidence-backed result |
|---|---|---|---|
| `invoke-1788091405247-3753-2e843c2e` | `t00J01` | `STOP` | the six-module circle-fold packet proves only the third conjunct; quotient-manifold/top-homology for the Klein product and rational sphere Lefschetz normalization are two independent absent foundations |
| `invoke-1788091407907-3754-d9387d48` | `t03J06` | `STOP` | the six-module packet proves the `7π` integral, but smoothness and the coordinate exterior-derivative value remain an independent missing theorem with no second consumer |
| `invoke-1788091410408-3755-148461f2` | `t94J06` | `CLOSED` after election | one coherent six-module circle-lifting/winding chain reaches the radius-disk obstruction; a zero-placeholder frozen fixture compiled |

Only `t94J06` was elected.  Implementation job
`invoke-1788091783980-3759-e0d38d5c` selectively promoted the six exact
historical `.lean/.md` pairs and committed the frozen closure as
`8efdc321217c27ad33308407f0baf578db5d4507`.  No mixed historical commit was
cherry-picked.  Independent review job
`invoke-1788092071400-3763-78a77595` returned `PASS`:

- all twelve promoted files match their specified historical blobs
  byte-for-byte;
- both frozen theorem statements are unchanged and placeholders fall `2 → 0`;
- all six direct compilations, the focused adapter build, and frozen Main
  compilation pass;
- scoped placeholder and axiom audits are clean, with only `propext`,
  `Classical.choice`, and `Quot.sound` used by principal declarations.

The final round-two decision is `CLOSED` for `t94J06`, with `t00J01` and
`t03J06` stopped rather than receiving partial historical infrastructure.

## Third portfolio round

The third round combined one remaining uptake audit with two probes of partial
or newly banked APIs:

| Job | Consumer | Decision | Evidence-backed result |
|---|---|---|---|
| `invoke-1788094173427-3862-c9a2987f` | `t98A05` | `CLOSED` after election | one coherent six-module packet proves the exterior derivatives, simplex integral, circle-period obstruction, and final conjunction; a zero-placeholder frozen fixture compiled |
| `invoke-1788094176057-3863-3bbcc70b` | `t94A10` | `STOP` | the historical chain proves local closedness, but nonexactness independently requires a global sphere-period/Stokes or de Rham theorem |
| `invoke-1788094178560-3864-3adb8687` | `t97J08` | `STOP` | the banked winding API closes uniqueness and the cross-derivative calculation compiles, but the beta-integral bridge requires a separate `C¹` regularity theorem for the covering lift |

Only `t98A05` was elected.  Implementation job
`invoke-1788094520582-3901-ed650d94` selectively promoted the six exact
historical `.lean/.md` pairs and committed the complete frozen closure as
`446ca98245e0379d0440eea9eb8ffbd113e9adf4`.  Independent review job
`invoke-1788094761055-3915-1d0e382a` returned `PASS`:

- all twelve promoted files match their nominated historical blobs
  byte-for-byte;
- all four frozen theorem statements and premises are unchanged, with
  placeholders `4 → 0`;
- six direct compilations, the 8,245-job focused build, and frozen Main
  compilation pass;
- the scoped placeholder and axiom audits are clean, with only `propext`,
  `Classical.choice`, and `Quot.sound` used by principal declarations.

The round closes `t98A05` without electing either the solid-angle nonexactness
program or smooth covering-lift regularity.

## Simply-connected sphere/product construction

After the low-cost whole-consumer uptake queue shortened, the next election
tested one reusable construction through three parallel read-only probes:

| Job | Probe | Decision | Result |
|---|---|---|---|
| `invoke-1788096708714-3934-ec4a501e` | generic products | `ELECT` | `SimplyConnectedSpace X` and `SimplyConnectedSpace Y` imply `SimplyConnectedSpace (X × Y)` by coordinate paths and path-homotopy projections; the exact theorem compiled |
| `invoke-1788096711721-3935-2177b3f1` | Euclidean spheres | `ELECT` | `Sⁿ` in `EuclideanSpace ℝ (Fin (n+1))` is simply connected for the sharp hypothesis `2 ≤ n`, using the banked pole-cover theorem and orthogonal-complement rank |
| `invoke-1788096714421-3936-144a4823` | frozen `t95J04` | `ELECT` for partial closure | the three simple-connectivity conjuncts align definitionally; a frozen fixture compiled with the existing single placeholder narrowed to Sard and the final product comparison |

Implementation job `invoke-1788097093918-3940-4f798b6e`, assigned to a fresh
agent outside the probe set, committed
`45304f7d38fe758471eb6cab2a039529b3e7c86b`.  It adds
`SimplyConnectedSphereProducts.{lean,md}` and supplies exactly the three
simple-connectivity conjuncts of `t95J04`.

Fresh independent review job `invoke-1788097372302-3941-269150b7` returned
`PASS`.  It confirmed the generic product proof is non-circular, the sphere
dimension/rank proof is sharp, the frozen statement is unchanged, and the one
source placeholder remains one declaration-level `sorryAx`.  Its residual is
now exactly the Sard/nullity/non-surjectivity/null-homotopy conjunct and
`S² × S⁴ ≄ S³ × S³`.  Direct target and frozen compilation, the 2,609-job
focused build, axiom audit, placeholder audit, and diff check passed.

This is a **bounded partial closure**, not a whole `t95J04` closure.  It banks
two reusable topology theorems without electing either remaining foundation.

## Medium-depth construction pipeline

With the selective-uptake queue shortened, three parallel probes established
the next layer of work:

| Priority | Job | Program | Decision and first milestone |
|---:|---|---|---|
| 1 | `invoke-1788099827204-4008-8baa6eb6` | `t97J08` smooth circle lifts | `GO`; a generic local-inverse descent theorem compiled, followed by a concrete `Circle.exp` specialization, normalized-loop regularity, and the existing beta-integral adapter |
| 2 | `invoke-1788099830885-4009-cfbf41e5` | `t95J04` Mayer--Vietoris product comparison | `GO`; one production MV segment suffices for `H₂(S³ × S³)=0`, using zero piece `H₂` and zero intersection `H₁`, with no Eilenberg--Zilber or Kunneth |
| 3 | `invoke-1788099833859-4010-0cd0ae16` | `t01J03` pseudococone target naturality | `GO`; postcomposition on `PseudoFunctorCocone` and the correctly oriented pseudopushout comparison natural isomorphism both compiled |

The shared-worktree schedule starts only one writer at a time while retaining
the other two programs with named next milestones.  `t97J08` is first because
its 3--4 commit plan can close a whole frozen consumer.  `t95J04` follows
because its four-stage MV program would leave only Sard.  The generic
pseudococone square is third: it has two consumers, but further target
naturality and source reconstruction remain downstream.

The first `t97J08` milestone was implemented by Agency job
`invoke-1788100317307-4056-18039c2b` as
`48eab2d3d37ee3ccdd5af51e66074bb274d891b3`.  Its generic
`contDiffAt_of_continuous_lift` theorem transfers regularity through an
explicit locally invertible smooth scalar map.  It does not claim that an
arbitrary covering lift is smooth.  Independent review job
`invoke-1788101335621-4162-288cacff` returned `PASS`: direct and focused builds,
scope, placeholder, axiom, and mathematical audits all passed.  The next
milestone is the rotated-imaginary-coordinate specialization to `Circle.exp`.

The complete program subsequently closed `t97J08`:

| Milestone | Implementation | Review | Result |
|---|---|---|---|
| local inverse descent | `invoke-1788100317307-4056-18039c2b`, commit `48eab2d3` | `invoke-1788101335621-4162-288cacff` | generic scalar lift regularity banked |
| `Circle.exp` specialization | `invoke-1788101541811-4187-24a1a35c`, commit `12fd086d` | `invoke-1788101861146-4224-3c0779e0` | continuous real lift of a smooth circle map is smooth via explicit rotated coordinate |
| frozen normalized-loop lift | `invoke-1788101973666-4238-6a3fff4f`, commit `55da22d8` | `invoke-1788102233127-4259-2dfa960c` | existing frozen hypotheses prove `LiftIsCOne` with no new premise |
| beta integral and frozen closure | `invoke-1788102430168-4269-9735b653`, commit `0ad32428` | `invoke-1788102692055-4289-7d72b209` | cross derivative, unique winding, beta integral, and final theorem compile; placeholders `4 → 0` |

The final reviewer checked all seven dependency modules, historical blob
identity, the complete import graph, frozen definition alignment, and the
`ExistsUnique` assembly.  The final decision is `CLOSED`.  The active writer
therefore advances to the queued `t95J04` Mayer--Vietoris program, while the
generic pseudococone target-naturality edge remains next in line.

The `t95J04` Mayer--Vietoris program then completed its bounded objective:

| Milestone | Implementation | Review | Result |
|---|---|---|---|
| pole-product cover geometry | `invoke-1788102877787-4298-8fc4b70b`, commit `e24d442b` | `invoke-1788103386802-4309-0a94e746` | genuine open cover of `S³ × S³`; pieces homotopy equivalent to `S³`; intersection homotopy equivalent to `S² × S³` |
| adjacent homology vanishing | `invoke-1788103500985-4313-06c4d5a7`, commit `6b59e2e6` | `invoke-1788103897297-4320-f672b33b` | generic simply-connected integral `H₁` vanishing and the concrete zero `H₂`/`H₁` inputs |
| one production MV segment | `invoke-1788104053440-4323-60a69151`, commit `f8feca24` | `invoke-1788104224845-4325-a777a95c` | degree parameter `1` gives `H₂(U) ⊞ H₂(V) → H₂(S³ × S³) → H₁(U ∩ V)` and proves the middle object zero |
| final product comparison | `invoke-1788104324431-4327-cb6f10a8`, commit `10cfb866` | `invoke-1788104546292-4331-6d3cd507` | compares retract-based nonzero `H₂(S² × S⁴)` with the MV vanishing result and compiles the last nonhomeomorphism conjunct |

This follows probe `invoke-1788099830885-4009-cfbf41e5` without introducing
Eilenberg--Zilber or Kunneth.  Together with commits `54fe6115` and
`45304f7d`, all three simple-connectivity and all three nonhomeomorphism
conjuncts now compile.  This remains a **bounded partial closure**: the single
frozen placeholder now contains only the Sard/nullity/non-surjectivity/
null-homotopy branch.  The active program advances to `t01J03` pseudococone
target postcomposition.

The first `t01J03` target-naturality milestone was implemented by Agency job
`invoke-1788104723752-4333-30cd2f57` as commit `67aa463e` and independently
reviewed `PASS` by job `invoke-1788104940330-4335-18ef87b5`.  It adds honest
target postcomposition for `PseudoFunctorCocone` and the natural isomorphism

```text
whiskeringRight H ⋙ pseudopushoutEquivalence(D).functor
  ≅ pseudopushoutEquivalence(C).functor ⋙ postcomposePseudoFunctorCoconeFunctor H.
```

The comparison uses inverse associators and explicitly transports descent
`eqToHom` terms through `H`; frozen `t01J03` still has exactly its two existing
placeholders.  This is one reviewed edge, not source reconstruction.  The next
action is a read-only probe of the immediately following strictification or
reconstruction equivalence layer.

## Updating the DAG

For an elected experiment, the DAG records:

- the frozen consumer and placeholder;
- the fixture or report path;
- the one candidate theorem;
- observed and proposed edges separately;
- the stop condition;
- the final decision and, if implemented, the closing commit.

The DAG is updated after synthesis, not after every intermediate lemma.
