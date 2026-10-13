# Topology build-loop independent review

Review only the first `:done-unreviewed` row printed above. The reviewer must
not be its author. Read the recorded commit rather than the working tree,
verify exact scope and fixture hash, rerun the acceptance gates, inspect theorem
orientations and representation boundaries, and recompute frozen statement
hashes and placeholder counts when applicable.

Judge an implementation against the fixture's frozen interface-axiom types
and the registered statement, not against declaration names the acceptance
lists in prose: the author designs supporting signatures (work-prompt.md,
"WHAT IS FROZEN"). PASS when every frozen axiom type is discharged in scope
with standard axioms only. A STOP that cites missing approved
signatures, the risk of inventing an interface, or a theorem absent from
Mathlib that the author did not attempt, is a deterministic defect: FAIL it
with the finding "extend Mathlib: state and prove the missing theorem in
scope" (work-prompt.md). A STOP after real progress (commit of compiled
supporting results, remaining theorems listed in `:missing-theorems`) or a
STOP with a compiled refutation is correct: PASS it.

On PASS, report the reviewer, job, reproduced commands, and findings. On a
deterministic defect, report the exact repair finding. Do not edit the ledger;
the supervisor owns its state transition. Never use an fNN agent.

End with one single-line `TOPOLOGY_RECEIPT_EDN` map. PASS uses
`{:outcome :pass :seat "codex-N" :job "invoke-..." :commands [...] :finding "..."}`;
FAIL uses `{:outcome :fail :seat "codex-N" :job "invoke-..." :finding "exact deterministic defect"}`.
The supervisor applies and commits the ledger transition.

Program rows (`:program true`): PASS a STOP that commits compiled, sorry-free,
standard-axiom progress toward the final theorem and lists its milestones;
FAIL one that commits nothing new since the last `:program-history` entry.

Blueprints (`*.blueprint.md`, see BLUEPRINTS.md): review the MATHEMATICS.
Check each node's statement is true as written, its proof uses only its
`uses:` nodes and stated hypotheses, every hypothesis of the final theorem
is used somewhere, and each Lean type is a faithful form of its statement.
FAIL with the counterexample or the missing hypothesis. Exception: a
hypothesis of a REGISTERED theorem (pinned in problems/STATEMENTS.json) that
problem.md itself states may go unused; the statement is frozen and faithful,
so record it as "unused, mandated by problem.md" and do not FAIL or STOP on it
(owner, 2026-10-13: t93J03's SemilocallySimplyConnected X).
