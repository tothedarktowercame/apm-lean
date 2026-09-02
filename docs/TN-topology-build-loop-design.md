# Topology build loop design

Date: 2026-09-02

Status: design for implementation

## Purpose

`topology-build-loop` is an unattended supervisor for the closure process in
`TN-topology-closure-experiments.md`.  It repeatedly selects one bounded edge
on an elected route to a frozen placeholder, runs one author or probe seat,
runs an independent reviewer, and advances the dependency graph only from a
checked receipt.

The loop exists so continuity does not depend on an interactive owner noticing
that a bell finished and issuing the next bell.  The supervisor owns the child
processes synchronously.  Agency is used for visibility and stop notification,
not as the loop's internal control flow.

The loop does not choose mathematics from a `sorry` count.  Its scheduling
authority is the topology DAG and the consumer-certification policy already
recorded in `TOPOLOGY-DEPENDENCY-DAG.md`.

## Proposed location

```text
holes/labs/topology-contract/
  topology-build-loop.sh
  build_step.bb
  worklist_check.bb
  worklist.edn
  work-prompt.md
  review-prompt.md
  runs/build-loop.log
  runs/<row>/<attempt>/receipt.edn
```

The loop and ledger belong in `apm-lean`; they operate only on the canonical
checkout.  They must not create ad-hoc worktrees or repair `.lake/packages`.

## Authorities

The loop has three distinct authorities:

1. `TOPOLOGY-DEPENDENCY-DAG.md` describes mathematical nodes, evidence-backed
   edges, current classifications, and closed consumers.
2. `worklist.edn` is the executable projection of the currently elected route.
   It may contain only nodes and edges already recorded in the DAG, plus a
   newly discovered prerequisite awaiting later DAG synthesis.
3. Git commits and compiled fixtures are proof receipts.  Ledger prose cannot
   override them.

The loop never rewrites the DAG.  It records completed work in the ledger and
notifies the portfolio owner.  The owner updates the DAG after a reviewed
milestone, a genuine stop, or consumer closure.  This retains the existing rule
that one owner synthesizes the DAG rather than several workers editing it.

## Ledger schema

```clojure
{:schema :topology/worklist-v1
 :campaign :t02A03
 :canonical-root "/home/joe/code/apm-lean"
 :canonical-packages "/home/joe/code/apm-lean/.lake/packages"
 :frozen-consumer "problems/t02A03/lean/Main.lean"
 :baseline {:git-sha "..."
            :placeholder-count 2
            :statement-hashes {"apm_t02A03_bridge_2" "..."}}
 :items
 [{:id :source-reconstruction
   :kind :reusable-theorem
   :dag-node "GENERIC TARGET-NATURAL SOURCE RECONSTRUCTION"
   :state :done
   :depends-on [:mapping-naturality]
   :consumer :t02A03
   :other-consumers [:t01J03]
   :representation {:source "functor categories"
                    :target "CategoryTheory.Equivalence"}
   :phase :implementation
   :scope ["ConstructionTargets/GenericTargetNaturalSourceReconstruction.lean"
           "ConstructionTargets/GenericTargetNaturalSourceReconstruction.md"]
   :acceptance {:declarations ["sourceEquivalence"]
                :consumer-residual "selected base-object transport only"
                :axioms :standard-only}
   :evidence {:fixture {:path "/tmp/GenericTargetNaturalSourceReconstructionProbe.lean"
                        :sha256 "..."}
              :commit "..."
              :review {:seat "codex-20" :result :pass :job "invoke-..."}}}]}
```

Required campaign fields pin the consumer, baseline commit, initial placeholder
count, and every frozen statement hash.  Required item fields name the DAG
node, edge kind, dependencies, representation at the seam, exact file scope,
acceptance condition, and expected change to the consumer residual.

Permitted edge kinds are:

- `:uptake`: compiled mathematics needs a canonical promotion;
- `:final-adapter`: a canonical theorem needs a frozen-facing transport;
- `:representation-comparison`: two honest representations need an
  equivalence or naturality square;
- `:reusable-theorem`: one absent shared mathematical edge;
- `:consumer-closure`: exact frozen placeholder replacement;
- `:documentation`: DAG and experiment-note synthesis after reviewed closure.

Permitted states are:

```text
:blocked :open :probing :probe-reviewed :implementing
:done-unreviewed :repair :done :needs-owner :superseded
```

Only one item may be `:probing`, `:implementing`, or `:repair`.  Only one item
may be `:done-unreviewed`.  This makes the canonical checkout single-writer and
prevents a reviewer from reading content that is still moving.

## Strategic invariants enforced by `worklist_check.bb`

The validator rejects a ledger unless all of the following hold:

1. Item ids are unique and every dependency exists; dependency edges are
   acyclic.
2. An `:open` row has all dependencies `:done`.
3. A `:blocked` row has at least one dependency not `:done`.
4. Every non-documentation row names one frozen consumer and the precise
   residual it is intended to shorten.
5. A `:reusable-theorem` row names at least two consumers, unless it is an
   explicitly recorded bounded exception under the DAG policy.
6. A `:representation-comparison` row names both representations and the exact
   direction of the proposed map, equivalence, or naturality square.
7. A probe has at most one candidate missing theorem.  A report with two
   independent missing foundations cannot transition directly to
   implementation.
8. Two consecutive completed infrastructure rows must show a changed
   consumer-facing fixture hash or a strictly smaller typed residual.  If not,
   the route becomes `:needs-owner` under the existing two-packet stop rule.
9. A closure row pins all frozen theorem hashes and an exact placeholder delta.
10. A reviewed row records different author and reviewer identities.
11. Evidence paths, fixture hashes, commits, and review jobs are present for
    the states that claim them.
12. No item may classify a fixed-target mapping equivalence as source
    reconstruction without an explicit target-naturality edge.

The validator also checks the live repository:

- the worktree is clean before probe, implementation, and review;
- `.lake/packages` resolves exactly to the canonical package authority; the
  canonical checkout owns the real directory, while any frame checkout must
  use the required symbolic link;
- recorded commits exist and touch only their declared scope;
- recorded fixture hashes still match;
- reviewed frozen statement hashes still match the campaign baseline;
- a `:done` closure has the declared placeholder count.

## Scheduling policy

The scheduler does not simply choose the first open row.  It orders eligible
rows according to the portfolio policy:

1. reviewed uptake already adjacent to a frozen consumer;
2. final adapters for banked canonical theorems;
3. one-edge `LOCAL-GO` or `API-GAP` probes;
4. reusable foundations supported by a successful consumer-facing probe and
   at least two named consumers;
5. representation-specific work only while its compiled fixture advances the
   named frozen consumer.

Within a class, prefer the row with the fewest unresolved edges to its frozen
placeholder, then the smallest declared scope.  Ties retain ledger order.  A
human election can pin one row with `:campaign-priority 0`; the validator
allows at most one such row.

The scheduler never automatically enters `FOUNDATION`, `SPEC-DEFECT`, or
`DEFERRED-REP` nodes.  Those classifications require an owner decision recorded
in the DAG and ledger.

## Iteration state machine

```text
validate ledger and repository
        |
        v
unblock satisfied dependencies
        |
        v
review pending commit? -- yes --> independent review
        |                              | PASS
        no                             v
        |                         mark :done
        v                              |
select highest-priority :open row <----+
        |
        +-- phase :probe ----------> read-only probe
        |                               |
        |                  GO ----------+--> create implementation row
        |                  REVISE ------+--> create exactly one prerequisite row
        |                  STOP --------+--> :needs-owner
        |
        +-- phase :implementation --> bounded author
                                        |
                                  committed receipt
                                        |
                                  :done-unreviewed
```

The next iteration always services `:done-unreviewed` before starting more
work.  `FAIL` returns the same row to `:repair` with the review finding.  A
deterministic repair is authored, committed, and reviewed again.  It does not
silently create a new mathematical row.

`REVISE` is legal only when the probe names one compiled prerequisite and
explains how it discharges the current residual.  The loop adds that
prerequisite immediately before the blocked row.  `STOP` is required for two
independent foundations, missing frozen hypotheses, representation scope
expansion, or any invariant conflict.

## Seat protocol

The supervisor invokes seats synchronously, following the working build loops:

```bash
timeout 5400 codex exec --skip-git-repo-check \
  --sandbox danger-full-access "$(cat "$prompt")"
```

Seat selection must satisfy:

- regular `codex-*` or Claude seats only; never `fNN`;
- author and reviewer are different identities;
- a reviewer never reviews a commit it authored;
- probes are read-only and implementations name exact writable scope;
- one invocation handles one row and returns one terminal receipt.

The prompt includes the selected row verbatim, its dependency receipts, the
current consumer residual, and explicit permission boundaries.  A seat may not
choose a different row.

Each seat ends its result with a single-line `TOPOLOGY_RECEIPT_EDN` map.  The
supervisor extracts it atomically into `runs/jobs/<job-id>.receipt.edn` and
preserves the full result beside it.  Required fields
include result, fixture hash, commands with exit codes, changed paths, commit,
axioms, warnings, placeholder delta, statement hashes, and the next residual.

## Result vocabulary

- `GO`: the entire requested probe packet compiles and is ready for bounded
  implementation.
- `REVISE`: exactly one named prerequisite compiles or is isolated; no other
  independent construction remains in the requested packet.
- `STOP`: the route crosses multiple independent foundations, lacks required
  hypotheses, changes representation scope, or triggers a strategic stop rule.
- `PASS`: independent review reproduces the claimed artifact and gates.
- `FAIL`: a deterministic defect exists in the reviewed commit.

These words are machine states, not rhetorical summaries.  The receipt schema
rejects `GO` without a complete compiled fixture, `REVISE` without one named
prerequisite, and `PASS` without a commit and reproduced gates.

## Gate profiles

Every implementation runs:

1. fixture SHA-256 verification and direct fixture compilation;
2. direct compilation of every changed Lean target;
3. the smallest focused `lake build` covering the changed targets and named
   collision consumers;
4. `#print axioms` audit of headline declarations;
5. forbidden scan for `sorry`, `admit`, `sorryAx`, new `axiom`, `opaque`, and
   `unsafe`;
6. `git diff --check` and exact-scope comparison;
7. commit and post-commit clean-worktree check.

A frozen closure additionally runs:

- before/after executable-placeholder counts;
- exact statement-hash checks;
- direct frozen `Main.lean` compilation;
- focused dependency build;
- full `lake build` when the final consumer is claimed closed;
- warning attribution, distinguishing new warnings from replayed dependency
  warnings.

Exit code 134 is classified as an environment abort and retried only after the
resource condition is diagnosed.  It is never recorded as a proof failure.

## Continuity, parking, and notification

The shell supervisor waits directly for each child process and therefore does
not require an interactive agent to remember a continuation.  It logs the
selected row, seat, PID, start time, heartbeat, exit status, and receipt path.

Agency still provides operator visibility:

- on start, send a typed notice naming campaign and row;
- on every reviewed milestone, send a concise progress bell;
- on `STOP`, `FAIL` that cannot be repaired, invalid ledger, timeout, signal,
  or exhausted retry budget, bell the Emacs owner with the reason and last 40
  log lines;
- on closure or an empty queue, bell `DONE` with counts and the closing commit.

If an interactive owner dispatches a one-off Agency job outside the supervisor,
the owner must park on its concrete job id.  The build loop itself must not use
fire-and-forget bells as dependency edges and must not poll an agent queue as a
substitute for waiting on the child it started.

## Stall and recovery rules

The loop stops and notifies when:

- the same row is selected three times without a state or residual change;
- a child exits successfully but emits no valid receipt;
- a receipt names paths outside the row scope;
- the canonical worktree is dirty at a phase boundary;
- the package authority is absent or incorrect;
- author/reviewer separation cannot be satisfied;
- a fixture path has changed content without a new recorded hash;
- the frozen statement or placeholder baseline drifts unexpectedly.

Recovery is explicit.  The owner repairs the ledger or repository, records any
changed authority, and restarts the supervisor.  The loop reads the ledger and
receipts and resumes from the first unreviewed or open row; it does not rely on
in-memory continuation state.

## Publication and campaign completion

There is no generated registry to publish after every topology row.  After a
reviewed milestone the loop reports DAG-ready evidence.  After a reviewed
consumer closure it creates one `:documentation` row whose acceptance is:

- add the consumer to “Problems closed during consolidation”;
- remove its obsolete partial-closure row;
- record the construction, repair, and independent-review chain;
- record fixture and frozen statement hashes, placeholder delta, warnings,
  builds, and axioms;
- commit only the DAG and process note.

The campaign is complete only when the frozen consumer is reviewed closed and
the documentation row is reviewed or owner-certified.  “No open rows” without
a reviewed consumer closure is a stopped or exhausted campaign, not success.

## Implementation slices

The design should be implemented in four independently testable slices:

1. Ledger schema, DAG/edge validation, dependency unblocking, and fixture/hash
   checks.
2. Synchronous author/reviewer runner, atomic receipts, exact-scope checks, and
   author/reviewer separation.
3. Strategic scheduler, `GO`/`REVISE`/`STOP` transitions, two-packet stop rule,
   and deterministic repair cycle.
4. Agency notifications, stall recovery, frozen-closure gate profile, and a
   dry-run replay of the completed `t02A03` chain.

The replay should consume recorded t02A03 receipts without rerunning proofs and
produce the same ordering from the initial bridge through `61f8ece4`, followed
by the documentation closure.  A second test should inject the stale
`postcomposeRepresentationFunctor` seam and show that the scheduler creates
one representation-comparison prerequisite rather than ending the campaign or
starting an unrelated foundation.
