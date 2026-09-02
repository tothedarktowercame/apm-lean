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
work rows in priority order: adjacent uptake/final adapters, then one-edge
`LOCAL-GO`/`API-GAP` probes, then explicitly owner-authorized foundations.
Append a fresh `:strategy-checkpoint` as the final vector item, depending on
every elected work-row id, so the campaign refills again after this portfolio.
Every inserted row must satisfy the full ledger schema and use a new id. An
ordinary replan may not return an empty tail. If no eligible row exists after
reading the entire DAG, return STOP with the exact owner election required;
do not label the campaign complete. Do not activate an unauthorized
`FOUNDATION`, `SPEC-DEFECT`, or `DEFERRED-REP`, and do not edit the DAG or
ledger directly.

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
