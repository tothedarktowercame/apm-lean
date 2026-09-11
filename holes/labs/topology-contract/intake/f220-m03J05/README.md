# F220 / m03J05 transferred from APM V3

Joe directed this transfer on 2026-09-11. The topology portfolio is being used
as the mathematical-infrastructure queue; the problem itself concerns functional
analysis, weak solutions and nonlinear operators.

Actual worklist entries are `:m03j05-f220-infrastructure-intake` (open probe) and
`:m03j05-f220-infrastructure-strategy` (blocked on its reviewed result). The
existing portfolio order is preserved. Enqueuing does not restart the topology
supervisor, which remained stopped when this packet was added.

Preserved authority: solver branch `exp/countdown-f220-m03J05-solver`, final commit
`c380d8ff286d5d5dacafdc200d4eddc0cdaa2eec`, 50 completed rounds, receipt
`a28fd032f06b54ba321e38a6f3983f90e9d60d01940ab48faeff998eccbb719a`.
The pinned `problems/m03J05/lean/Main.lean` SHA256 is
`244587aa6e02da7ad37d1af01c039355c952a53d1da58ad292cec4cbacb3946d`.
The source commit exists; its theorem/placeholder inventory was inspected, but
no fresh elaboration of this problem is claimed.

Three frozen bridges remain. Bridge 1 needs compactness and mixed spectral/
Fredholm classification. Bridge 2 needs the direct Frechet remainder theorem
and energy assembly. Bridge 3 needs translation from the banked forced-contraction
fixed-point equation through the derivative parametrization and adjoint identity
to the frozen weak predicate; uniqueness is already present according to the
retained solver receipt. The intake must validate that account, produce a DAG,
and identify the smallest next theorem instead of repeating an unbounded solve.

`rows.edn` retains the inserted rows. The full worklist validator passed with
623 items: 609 done, 1 needs-owner, 6 superseded, 3 open and 4 blocked. Historical
F220 receipts and the solver branch are preserved; transfer does not claim
mathematical completion or invalidate its original APM history.
