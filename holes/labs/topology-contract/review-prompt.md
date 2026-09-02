# Topology build-loop independent review

Review only the first `:done-unreviewed` row printed above. The reviewer must
not be its author. Read the recorded commit rather than the working tree,
verify exact scope and fixture hash, rerun the acceptance gates, inspect theorem
orientations and representation boundaries, and recompute frozen statement
hashes and placeholder counts when applicable.

On PASS, report the reviewer, job, reproduced commands, and findings. On a
deterministic defect, report the exact repair finding. Do not edit the ledger;
the supervisor owns its state transition. Never use an fNN agent.

End with one single-line `TOPOLOGY_RECEIPT_EDN` map. PASS uses
`{:outcome :pass :seat "codex-N" :job "invoke-..." :commands [...] :finding "..."}`;
FAIL uses `{:outcome :fail :seat "codex-N" :job "invoke-..." :finding "exact deterministic defect"}`.
The supervisor applies and commits the ledger transition.
