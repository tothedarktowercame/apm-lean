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

## Updating the DAG

For an elected experiment, the DAG records:

- the frozen consumer and placeholder;
- the fixture or report path;
- the one candidate theorem;
- observed and proposed edges separately;
- the stop condition;
- the final decision and, if implemented, the closing commit.

The DAG is updated after synthesis, not after every intermediate lemma.
