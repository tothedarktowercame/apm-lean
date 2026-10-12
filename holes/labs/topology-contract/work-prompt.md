# Topology build-loop row

Work only on the row printed above. Read `TOPOLOGY-ROUTES.md` (the loops'
guide since 2026-09-28; it replaces `TOPOLOGY-DEPENDENCY-DAG.md` for elections),
the per-problem routes in `holes/labs/topology-routes/routes-{1,2,3}.md`, and
the row's dependency receipts.

For `:phase :probe`, remain read-only and return exactly one of GO, REVISE, or
STOP under the definitions in `docs/TN-topology-build-loop-design.md`. GO needs
a complete placeholder-free compiled fixture. REVISE needs exactly one named
compiled prerequisite. STOP names the exact mathematical, hypothesis, or
representation boundary.

For `:phase :strategy`, reread `TOPOLOGY-ROUTES.md`, the routes files and the
reviewed dependency receipts. 
LEMMA DAG (Joe, 2026-10-10: "previous loops maintained a DAG so they could
keep track of the priority of lemmas"). The ledger holds rows of kind `:lemma`
-- missing theorems, state `:backlog` until a reviewed row proves them, then
`:banked` -- with `:depends-on` edges between lemmas and `:consumer` /
`:other-consumers` naming the problems that need them. Every checkpoint:

1. Run `bb holes/labs/topology-contract/build_step.bb priorities <this ledger>`.
   It first prints each open problem's banked/backlog lemma counts. A
   problem whose backlog is 0 has a complete route: elect its closure
   adapter (or closure probe) BEFORE any lemma, under rule 0. Lemmas exist to
   close problems (Joe, 2026-10-10); between closures, steer toward the
   problem with the fewest backlog lemmas left. It then
   ranks backlog lemmas: ready ones (dependencies banked) first, then by
   how many open registered problems each unblocks, then by how close those
   problems are to closing. Put the top of that ranking in your `:finding`.
   Last it prints AREAS across both loops: each theory area (a shared tag
   from TOPOLOGY-ROUTES.md, or a lemma's `:area`) with the open registered
   problems it serves -- including the other loop's and unassigned ones --
   its banked/backlog lemmas and its ConstructionTargets modules.
   BALANCE (Joe, 2026-10-10): per-problem readiness finishes problems that
   are nearly closed, but a single problem can absorb lemma after lemma.
   Elect at most one closure-directed row per checkpoint (rule 0); fill the
   remaining slots from the highest-impact areas that serve at least one of
   this loop's problems, building each area's results once, in one
   ConstructionTargets module per area, at the generality its problems use.
2. Maintain the DAG: every lemma carries `:area`; tag any lemma printed as
   UNTAGGED (prefer an existing TOPOLOGY-ROUTES.md tag; reuse one spelling
   per area). Return `:lemmas` (same map shape as `:missing-theorems`,
   with `:depends-on` names) to add lemmas a route needs, split a lemma that
   is too large for one row into smaller ones it depends on, or add edges.
   On the first checkpoint after 2026-10-10, also import the non-BANKED nodes
   of `TOPOLOGY-DEPENDENCY-DAG.md` that lie on this loop's open problems.
3. Elect work rows for the top ready lemmas: give each `:implements-lemma
   <lemma id>` (and `:depends-on` the lemma ids it uses). Its PASS banks the
   lemma and unblocks everything waiting on it. A PASS on a STOP does not:
   the row becomes `:stopped`, its lemma stays backlog and its dependents stay
   blocked. Read a `:stopped` row's reason and elect the work it names. Rule 0 (close nearly-closed
   problems first) still comes first.

A `:needs-owner` row or a stop-after-two is NOT a hold on its problem; re-route
it through the DAG. A checkpoint may not answer terminal while an open problem
of this loop has backlog lemmas. Restrategising is expected at every
checkpoint. Elect only from this loop's half of
`TOPOLOGY-ROUTES.md` and follow its election rules; where the text below says
"the DAG", read `TOPOLOGY-ROUTES.md` and the routes files. Measure placeholder changes, typed residual changes, infrastructure
packet counts, and STOP/PASS outcomes. Return `:outcome :replan` with a
`:replacement-items` vector containing a newly elected portfolio from the
complete DAG—not merely descendants of the rows just completed. Elect 1-5
work rows in STRATEGIC ORDER under the standing portfolio policy below.
Append a fresh `:strategy-checkpoint` as the final vector item, depending on
every elected work-row id, so the campaign refills again after this portfolio.
Every inserted row must satisfy the full ledger schema and use a new id. An
ordinary replan may not return an empty tail. Do not edit the DAG or ledger
directly.

GO and REVISE are probe outcomes. A `:phase :strategy` row answers with
`:replan`, or with a STOP that names a genuine refutation. A GO on a strategy
row is refused before it reaches the ledger: GO moves a row to
implementation, and a strategy checkpoint cannot be one.

A row with `:kind :representation-comparison` must additionally state all
THREE parts of the comparison, or admission rejects it and the loop stops:

    :representation {:source    "what is being compared, on one side"
                     :target    "what it is being compared to"
                     :direction "which way the identification runs, and what
                                 kind of identification it is"}

`:source` and `:target` alone are not enough. `:direction` is the orientation
and it is the field that gets forgotten: it stopped the loop on 2026-09-08 at
09:33 on the campaign's second comparison row. Say it the way the first one
did -- "Exact equality from the target-image fiber representation to the
source-fiber coordinate-image representation" -- naming the relation as well
as the direction. Only you can supply it; nobody downstream can infer it from
the other two fields without inventing mathematics.

APPROVED STATEMENTS (Joe, 2026-09-28). Work only toward problems whose
statement is in `problems/STATEMENTS.json`; admission refuses a row whose
consumers are all unregistered. Never change a registered theorem's statement
or any definition it uses: the loop checks every registered fingerprint each
iteration (`python3 scripts/statement-registry.py check`) and stops on a
mismatch. Never write `problems/STATEMENTS.json`, `scripts/statement-registry.py`
or `holes/labs/statement-registry/`. If a statement looks unprovable or wrong,
STOP and say why; an outside grader decides, not the loop.

NEED-DRIVEN ELECTION (Joe, 2026-09-10; every strategy checkpoint, both
loops). Infrastructure is built because an open frozen problem needs it to
close, and for no other reason.

a. Keep each open problem's route. For every open frozen problem the DAG
   names, list its remaining placeholders (comment-stripped, as in rule 0)
   and, for each placeholder, the chain of missing theorems or constructions
   between it and what is already banked. Put these routes in the receipt's
   `:finding`, updated from the previous checkpoint's.
b. Elect only steps on a route. A work row is eligible only if it supplies a
   missing step on the route of at least one open problem. Name that problem
   as `:consumer` (others that need the same step as `:other-consumers`) and
   say in the acceptance which placeholder and which route step it supplies.
   Infrastructure that no open problem is waiting on is not elected, however
   natural or general; list it in the finding as deferred.
c. Build exactly what is needed. State each result at the generality its
   named consumers use. Do not generalise for completeness; a later consumer
   that needs more will elect the extension then.
d. Build shared steps once. When two or more open problems need overlapping
   steps, build the common part once, at the generality that covers exactly
   those problems, and name them all. Before electing any step, search
   `ConstructionTargets/` and the DAG's banked results for something that
   already supplies it, and reuse that rather than rebuild it.
e. Attempt a problem as soon as its route is complete. When every step on a
   problem's route is banked, elect its closure probe or adapter first, under
   rule 0. This holds for every problem, `DEFERRED-REP` ones such as `t00J02`
   included.

Admission enforces (b) and part of (d): `build_step.bb` rejects a replan any
of whose non-documentation work rows names no frozen problem that still has
placeholders, and a `:reusable-theorem` row naming fewer than two such
problems without a `:bounded-exception`. A problem-prefixed label such as
`:t02A05-moment-reduction` counts as naming `t02A05`; a label such as
`:circle-fundamental-class` names no problem.

STANDING PORTFOLIO POLICY (Joe, 2026-09-06; supersedes the prior
owner-authorization gate). The campaign runs the DAG in strategic order until
every consumer problem is closed. `FOUNDATION`, `SPEC-DEFECT` and
`DEFERRED-REP` rows are STANDING AUTHORIZED: electing one needs no further
owner approval. Rank the rows NEED-DRIVEN ELECTION admits and elect the top
rows by, in order:

0. CLOSE WHAT IS NEARLY CLOSED FIRST. Before ranking anything, count the
   remaining placeholders in each consumer problem the DAG names, with
   comments stripped -- a bare `rg` for `sorry` matches PROSE, which is how
   b93J03 read as unfinished while its branch was byte-identical:

       python3 -c 'import re,sys; t=open(sys.argv[1]).read();
       t=re.sub(r"/-.*?-/"," ",t,flags=re.S); t=re.sub(r"--[^\n]*"," ",t);
       print(len(re.findall(r"(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])",t)))' \
         problems/<id>/lean/Main.lean

   If any consumer is within TWO placeholders of closing, elect the adapter
   that closes it AHEAD of every foundation. Elect exactly one such adapter
   per checkpoint, so the foundations keep advancing behind it.

   This rule is here because the ranking below cannot elect one on its own.
   An adapter unblocks exactly one problem by definition, so it never outranks
   a foundation on criterion 1, and the campaign applied that faithfully for
   eight days. Measured 2026-09-09: 349 rows completed, ConstructionTargets
   grown from 257 to 588 modules, and not one topology problem's placeholder
   count changed -- 52 problems stood at zero sorries on 2026-09-02 and 52
   stand there now. t93A04, named as consumer by 330 of those rows, still
   carries the single placeholder it had on 2026-08-08, and its file has not
   been edited since.

   `TN-topology-foundational-programs.md` states the counterweight, in a
   document this checkpoint does not otherwise read: "the program is not
   considered successful merely because a sequence of ConstructionTargets
   compiles." Closing one named problem is what shows the infrastructure was
   worth building. If the nearest adapter CANNOT be built from what exists,
   STOP and name exactly what is missing -- that is a more useful result than
   another foundation, and it is not a refutation, so say which it is.

1. how many open problems' routes the row lies on (most first);
2. how little work it is (simplest first), preferring one coherent theorem or
   one bounded construction.

Except under rule 0, a `FOUNDATION` that unblocks several consumers outranks
an adapter that unblocks one. `STOP :needs-owner` is NO LONGER a valid
strategy outcome and must not be returned: if the only remaining rows are
foundations, specification repairs or deferred representations, ELECT THE
BEST NEEDED ONE under the ranking above and proceed. The prior gate inverted this
policy -- it stopped the campaign precisely when the remaining work was the
work that matters -- and it is withdrawn. Only two conditions end the
campaign: every consumer problem closed, or a row whose mathematics is
genuinely refuted, which is reported as a STOP naming the refutation, not as
an election request.

WHAT IS FROZEN, AND WHAT YOU WRITE (owner, 2026-10-10). Two things are
frozen: the consumer problem's registered statement, and the TYPE of each
interface axiom in the row's fixture. The fixture's axiom names exactly what
the row owes; discharging it means a theorem or definition in `:scope` whose
type is that axiom's type, built from standard axioms only. Everything else
the acceptance lists in prose -- helper structures, intermediate lemmas, the
names and signatures of supporting declarations -- is yours to design. Pick
types that make the frozen axiom's type provable, state them in the receipt,
and implement them. Choosing those signatures is NOT inventing the public API.

FOUNDATION PROGRAMS (Joe, 2026-10-11). A row with `:program true` is a
multi-job construction of one foundation many problems need. It has no frozen
fixture: you design every supporting declaration; only the final theorem's
type in `:acceptance` is fixed. Each job: read `:continue-from` and
`:program-history`, build on the last commit (never restart), commit what
compiles (no sorry, standard axioms only), and list each milestone in
`:missing-theorems` with `:status :proved` once it compiles -- that banks it.
Return DONE-UNREVIEWED only when the final theorem compiles; otherwise STOP
with the commit. A reviewed program STOP reopens the row, so stopping is how
a program job ends, not a failure. Strategy checkpoints may not supersede
program rows; they may elect rows that consume banked milestones.

BLUEPRINTS (Joe, 2026-10-11; holes/labs/topology-contract/BLUEPRINTS.md).
A foundation is formalised from a reviewed blueprint
`ConstructionTargets/<Foundation>.blueprint.md`, written after the route
audits that name it (~/notes/closer/audits/). A program or row whose
acceptance names a blueprint that does not exist yet writes it first, as its
whole job (commit the .md, STOP "blueprint written"); a reviewed blueprint's
nodes are the program's milestones, and a STOP names the node it is stuck on.
A strategy checkpoint may elect a multi-day foundation row only when a
reviewed blueprint backs it; otherwise it elects the blueprint.

EXTEND MATHLIB; DO NOT STOP FOR A MISSING THEOREM (Joe, 2026-10-10). When the
proof needs a theorem that Mathlib and `ConstructionTargets/` lack -- a
covering restricted to a path component, a fundamental-domain homeomorphism,
a homotopy equivalence to a model -- state it and prove it yourself, in the
row's scope, as Mathlib would: general enough for this row's consumers, no
more. That is the work, not an obstacle to it. Name every such theorem in the
receipt's `:missing-theorems` vector, one map per theorem:

    {:name "IsCoveringMap.restrictPathComponent"
     :type "<full Lean statement>"
     :status :proved | :partial | :not-started
     :consumers [:t99J01]
     :depends-on ["<names of other missing theorems this one needs>"]
     :area "<theory area: a TOPOLOGY-ROUTES.md shared tag, e.g. covering-subgroup-correspondence>"}

Each entry becomes (or updates) a node in the ledger's lemma DAG, matched by
name. `:status :proved` banks that node when this row's review passes.

If the job ends before the row is complete, commit what compiles (no `sorry`,
no axiom beyond the fixture's frozen ones), list the rest with
`:status :partial` or `:not-started`, and return STOP: the next strategy
checkpoint splits the list into rows. The list is a record for strategy, never
the reason for stopping early.

The only STOP that ends work on a row's mathematics is a refutation: a frozen
type that is false or needs a missing hypothesis, with a compiled
counterexample or the exact hypothesis.

For implementation or repair, modify only `:scope`, verify the recorded fixture
hash, run every acceptance gate, and commit the scoped change. Report author,
commit, fixture, commands and exit codes, warnings, axioms, changed paths,
placeholder delta, statement hashes, and next consumer residual in the receipt.
For a deliberately inverted diagnostic such as an `rg` no-match scan, retain
the real `:exit` and add `:expected-exit` with that same value. Other commands
default to expected exit zero.
Keep corrected exploratory failures in a separate top-level `:diagnostic-history`
vector, preserving their actual exit codes and explaining the correction. Only
final acceptance checks belong in `:commands`. A `:stage` label does not exempt
a command from gate validation. Never mark a failed compile as expected merely
because a later compile succeeded; record the successful rerun in `:commands`
and the initial failure in `:diagnostic-history` instead.
Do not edit the ledger; the supervisor applies and commits its transition.
Never weaken an invariant or use a workaround. Never use an fNN agent.

End with exactly one single-line EDN receipt prefixed `TOPOLOGY_RECEIPT_EDN `.
For example, a successful probe ends with
`TOPOLOGY_RECEIPT_EDN {:outcome :go :fixture {:path "/tmp/X.lean" :sha256 "..."} :commands [{:cmd "lake env lean /tmp/X.lean" :exit 0}] :residual "bounded adapter"}`.
A GO receipt also supplies `:implementation {:scope [...]}` and any refined
acceptance fields needed for the bounded author packet.
A revision uses `:outcome :revise` and supplies one complete `:prerequisite`
ledger item. An implementation uses `:outcome :done-unreviewed` and includes
`:author`, `:commit`, `:changed-paths`, gates, warnings, axioms, and residual.
The supervisor, not the seat, applies and commits the ledger transition.
A STOP receipt also includes `:seat`, `:reason`, and the commands supporting
the boundary; it is independently reviewed as a scheduling result. A strategy
receipt uses `:outcome :replan`, `:seat`, `:commands`, `:finding`, and
`:replacement-items`.
