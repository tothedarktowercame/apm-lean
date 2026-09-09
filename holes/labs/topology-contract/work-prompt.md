# Topology build-loop row

Work only on the row printed above. Read `TOPOLOGY-DEPENDENCY-DAG.md`,
`docs/TN-topology-closure-experiments.md`, and the row's dependency receipts.

For `:phase :probe`, remain read-only and return exactly one of GO, REVISE, or
STOP under the definitions in `docs/TN-topology-build-loop-design.md`. GO needs
a complete placeholder-free compiled fixture. REVISE needs exactly one named
compiled prerequisite. STOP names the exact mathematical, hypothesis, or
representation boundary.

For `:phase :strategy`, reread the current DAG and the reviewed dependency
receipts. Measure placeholder changes, typed residual changes, infrastructure
packet counts, and STOP/PASS outcomes. Return `:outcome :replan` with a
`:replacement-items` vector containing a newly elected portfolio from the
complete DAG—not merely descendants of the rows just completed. Elect 1-5
work rows in STRATEGIC ORDER under the standing portfolio policy below.
Append a fresh `:strategy-checkpoint` as the final vector item, depending on
every elected work-row id, so the campaign refills again after this portfolio.
Every inserted row must satisfy the full ledger schema and use a new id. An
ordinary replan may not return an empty tail. Do not edit the DAG or ledger
directly.

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

STANDING PORTFOLIO POLICY (Joe, 2026-09-06; supersedes the prior
owner-authorization gate). The campaign runs the DAG in strategic order until
every consumer problem is closed. `FOUNDATION`, `SPEC-DEFECT` and
`DEFERRED-REP` rows are STANDING AUTHORIZED: electing one needs no further
owner approval. Rank the whole DAG and elect the top rows by, in order:

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

1. how many downstream consumer problems the row unblocks (most first);
2. how little work it is (simplest first), preferring one coherent theorem or
   one bounded construction.

Except under rule 0, a `FOUNDATION` that unblocks several consumers outranks
an adapter that unblocks one. `STOP :needs-owner` is NO LONGER a valid
strategy outcome and must not be returned: if the only remaining rows are
foundations, specification repairs or deferred representations, ELECT THE
BEST ONE under the ranking above and proceed. The prior gate inverted this
policy -- it stopped the campaign precisely when the remaining work was the
work that matters -- and it is withdrawn. Only two conditions end the
campaign: every consumer problem closed, or a row whose mathematics is
genuinely refuted, which is reported as a STOP naming the refutation, not as
an election request.

For implementation or repair, modify only `:scope`, verify the recorded fixture
hash, run every acceptance gate, and commit the scoped change. Report author,
commit, fixture, commands and exit codes, warnings, axioms, changed paths,
placeholder delta, statement hashes, and next consumer residual in the receipt.
For a deliberately inverted diagnostic such as an `rg` no-match scan, retain
the real `:exit` and add `:expected-exit` with that same value. Other commands
default to expected exit zero.
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
