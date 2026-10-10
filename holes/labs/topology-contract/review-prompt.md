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
with standard axioms only. A STOP that cites only missing approved
signatures, or the risk of inventing an interface, is a deterministic
defect: FAIL it with the finding "design the supporting signatures and
discharge the frozen axiom type".

On PASS, report the reviewer, job, reproduced commands, and findings. On a
deterministic defect, report the exact repair finding. Do not edit the ledger;
the supervisor owns its state transition. Never use an fNN agent.

End with one single-line `TOPOLOGY_RECEIPT_EDN` map. PASS uses
`{:outcome :pass :seat "codex-N" :job "invoke-..." :commands [...] :finding "..."}`;
FAIL uses `{:outcome :fail :seat "codex-N" :job "invoke-..." :finding "exact deterministic defect"}`.
The supervisor applies and commits the ledger transition.
