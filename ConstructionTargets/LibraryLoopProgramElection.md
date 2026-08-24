# Initial Library Loop construction-program election

Status: elected program portfolio for the first Library Loop qualification.
This document elects **areas of reusable construction**, not demonstrator
problems.  Problem selection is a later, state-bound decision made from a
problem's current residual obligation, green local gates, and an explicit
promotion witness.

## Evidence and decision rule

This election is bound to repository commit
`605c195b97bcdeb7f288bcbde25c217ada3b6c13` (2026-08-24).  It uses:

- the unresolved structured obstruction census summarized in
  `ObstructionAreaPrograms.md`;
- the concrete completion frontiers in `SingularHomologyConcrete.md` and
  `FundamentalGroupConcrete.md`;
- the realised local ConstructionTargets inventory; and
- the Library Loop acceptance contract in
  `futon3c/holes/technotes/TN-fable-library-loop-review.md` at futon3c commit
  `0487468f`.

The generated dependency map is deliberately not used as a ranking oracle.
Its validation finds that frozen statements recover only 6/38 realised import
edges, while current obstruction records describe the present wall rather
than cumulative infrastructure use.  Counts establish repeated demand, not
cost, causal necessity, or probability of closure.  A program is elected only
when repeated demand is joined by (a) a reusable dependency trunk, (b) a
locally testable next promotion, and (c) a materially different qualification
surface from the other slots.

At this snapshot the leading structured counts are singular homology 23,
fundamental group 14, covering space 13, orientation 9, and transversality 7.
Important co-occurrences expose dependencies rather than extra independent
votes: fundamental group/singular homology occurs 6 times,
covering/fundamental group 5, covering/orientation 5,
Mayer--Vietoris/singular homology 4, and van Kampen/fundamental group 4.

Inclusion requires all of the following:

1. more than a one-problem adapter is plausibly reusable;
2. the dependency order is stated rather than hidden by a composite label;
3. one promotion test can be exercised entirely in the persistent apm-lean
   workspace with targeted builds, consumer elaboration, and axiom audit; and
4. progress can be judged as a reduction of a stable mathematical obligation,
   not merely as another banked interface.

Exclusion from the hard slate means “not in the first five concurrent program
slots,” not “unworthy of library construction.”  Low count alone is not a
rejection, and high count alone is not admission.

## Hard five-slot slate

| Slot | Elected construction program | Dependency and overlap boundary | Locally exercisable promotion test |
|---|---|---|---|
| 1 | **Concrete singular homology trunk** | Owns relative chains, excision, Mayer--Vietoris, cellular comparison, concrete circle/sphere computations, and later Kunneth.  `mayer-vietoris`, `cellular-homology`, `excision`, and `kunneth` are milestones of this program, not separate slate votes. | Target-build `ConstructionTargets.SingularHomologyConcrete` and every import-graph consumer changed by the increment; elaborate one fixture/real consumer that uses the newly promoted theorem on a concrete space; print axioms for the headline isomorphism, generator, and vanishing result and require no `sorryAx`.  The next frontier test is the two-contractible-arcs computation of genuine `H₁(S¹) ≅ ℤ`, not the already-complete cellular model. |
| 2 | **Concrete fundamental groups and van Kampen** | Starts with the circle computation, then transport/products, open-cover van Kampen, presentations, and surfaces.  `van-kampen` is a dependent layer of this trunk.  Cover classification may consume it but does not own it. | Build the promoted fundamental-group module and its closure; elaborate an anti-vacuity fixture proving both `FundamentalGroup Circle 1 ≃* Multiplicative ℤ` and the induced named nontriviality instance.  Before advancing to the next layer, a second fixture must compute `π₁(S¹ ∨ S¹)` as the free group with generator-compatible maps.  Audit both headline declarations for `sorryAx`. |
| 3 | **Finite covering spaces, subgroup classification, and monodromy** | Depends on slot 2 for induced-range and subgroup statements.  Its orientation-character facet consumes the homological/manifold orientation API but does not absorb the whole orientation program.  It remains separate because local trivializations, fibers, deck actions, and monodromy are distinct executable infrastructure. | Build the covering module/closure and elaborate a fixture constructing a concrete connected double cover, proving exact two-point fibers, identifying the induced fundamental-group range with its classifying subgroup, and distinguishing it from the disconnected cover.  Require a named deck/monodromy anti-vacuity witness and axiom-clean promoted declarations. |
| 4 | **Homological orientation and transverse-preimage duality** | This is a deliberately bounded integration program: sphere/top homology and orientation feed the already-realised preimage-duality modules.  It does **not** claim to cover manifold Sard or general parametric transversality.  It depends on slot 1 and shares orientation-character consumers with slot 3. | Target-build the exact import closure of `OrientedSurfacePreimageDuality`, `TransversePreimageDuality`, and `DiskBoundedPreimageDuality`, then elaborate a fixture that instantiates the current producer boundary and derives the disk-bounded elimination theorem for a concrete oriented surface/map.  Require fresh oleans before consumer elaboration and axiom audits with no `sorryAx` on every promoted producer theorem. |
| 5 | **Intersection theory and product pairings** | Depends on slot 1 for fundamental classes and on its Kunneth milestone for product calculations.  Orientation conventions are consumed from slot 4.  It remains separate because geometric/homological comparison and self-intersection are a distinct API and already have a realised `ConstructionTargets.Intersection` seam. | Build `ConstructionTargets.Intersection` plus transitive consumers; elaborate one concrete transverse-intersection parity fixture and one product/self-intersection fixture whose non-bounding conclusion uses the promoted pairing.  Audit the comparison and nonvanishing declarations, not just a problem-level wrapper, for absence of `sorryAx`. |

These are portfolio slots.  They do not authorize selecting `t91A05`,
`t00J02`, or any other problem merely because it appears in an evidence table.
For example, the fundamental-group slot's first local promotion naturally has
`t91A05` as a possible consumer, while the slot itself persists beyond that
problem to van Kampen and surface presentations.

## Expanded qualification slate

The following programs should be qualified after the hard five, or earlier if
a hard-slot program lacks a green, locally executable promotion witness.

| Priority | Program | Why it is not silently covered by the hard five | Required local promotion test |
|---|---|---|---|
| Q1 | **Manifold Sard and parametric transversality** | Slot 4 covers transverse-preimage duality after suitable geometric input; it does not supply Sard or the incidence-submanifold theorem. | Build a promoted manifold-Sard theorem and elaborate two fixtures: a nonempty-domain regular-value consequence and a parameterized family whose good parameters satisfy the required almost-everywhere/dense ruling. |
| Q2 | **Differential forms and Stokes** | Its six records and two Stokes records form a substantial but largely independent calculus/integration trunk. | Build the bundled `extDeriv`/integration closure and elaborate a compact-support or surface fixture in which the boundary integral is computed.  Audit the Stokes headline and the concrete nonzero period/non-exactness witness. |
| Q3 | **Integral degree-one cohomology** | It consumes singular homology but requires circle representability and relative adjustment not furnished by slot 1. | Elaborate a fixture constructing a circle-valued map from a primitive integral `H¹` class and a second fixture preserving the prescribed restriction; audit representability and adjustment declarations. |
| Q4 | **Analytic pilots: complex, measure/integral, Fourier** | These are three different programs; their small counts do not justify merging them into a fictitious common library. | Complex: a reusable Rouché zero-count fixture.  Measure: a one-sided endpoint FTC fixture.  Fourier: the concrete interval-transform/convolution implication with injectivity.  Each pilot must pass its own target build, consumer elaboration, and axiom audit before election to a sustained slot. |
| Q5 | **Circle degree theory** | The sole structured record is precise, but the program is narrower than the hard five and may reuse orientation/degree work. | Compute the degree of the integer-multiplication map on the additive circle and use it in a homotopy-classification fixture, with axioms printed for both declarations. |

The expanded slate is a qualification queue, not a promise to run all programs
simultaneously.  Q1 is the first alternate because it exercises a genuine gap
left by slot 4; Q2 follows because it has repeated independent demand.  The
analytic pilots remain separate until local evidence demonstrates reusable
trunks.

## Problem-selection boundary

After an area is elected, a demonstrator problem may be nominated only by a
separate record containing:

- the current frozen statement and exact residual declaration/obligation;
- the elected program and precise increment expected to reduce it;
- the base and candidate Git SHAs;
- the targeted build, transitive-consumer, problem `Main.lean`, sorry-count,
  and axiom-audit commands; and
- a semantic promotion witness that would distinguish a reduced obligation
  from an equivalent reformulation.

The Library Loop's independent strategy reviewer remains authoritative about
reduction.  A successful target build or `:partial-banked` ruling is progress,
not slate success.  Only the ordinary status-recompute path reaching `:closed`
changes the demonstrator scoreboard.

## Qualification of the loop, separate from qualification of a program

No elected program waives the runner acceptance gates.  Before this portfolio
is called operational, the files-only runner must complete the technote's
20-turn dry run and checkpoint without futon3c repair commits; survive kills at
turn, gate, review, and bank boundaries without duplicate turns or banks;
rebuild changed ConstructionTargets before consumer elaboration (the missing
olean regression); pause on two independently reviewed non-reductions of the
same stable obligation; and update the demonstrator ledger only through
ordinary status recomputation.

Thus there are two independent verdicts:

1. **program promotion:** the locally exercisable mathematical test above is
   green and axiom-clean; and
2. **demonstrator success:** a separately selected problem is `closed`.

Neither verdict can be substituted for the other.
