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
`:replacement-items` vector containing the newly elected tail. Every inserted
row must satisfy the full ledger schema. Do not activate `FOUNDATION`,
`SPEC-DEFECT`, or `DEFERRED-REP` work automatically, and do not edit the DAG or
ledger directly.

For implementation or repair, modify only `:scope`, verify the recorded fixture
hash, run every acceptance gate, and commit the scoped change. Report author,
commit, fixture, commands and exit codes, warnings, axioms, changed paths,
placeholder delta, statement hashes, and next consumer residual in the receipt.
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
