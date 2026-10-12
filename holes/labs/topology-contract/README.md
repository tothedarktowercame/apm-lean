# Topology build loops

Codex seats formalize the open topology problems in `problems/` by working
through a ledger of rows: lemmas, adapters, foundation programs and strategy
checkpoints. Every row's result is reviewed by a second seat before the ledger
records it. Three loops run in parallel, each with its own ledger:

| unit    | ledger          | runs dir | seats (owner / author+repair / review / probe+strategy) |
|---------|-----------------|----------|-----------------------------------------------|
| `topo1` | `worklist.edn`  | `runs/`  | topo-1 / topo-2 / topo-3 / topo-4             |
| `topo2` | `worklist2.edn` | `runs2/` | topo-5 / topo-6 / topo-7 / topo-8             |
| `topo3` | `worklist3.edn` | `runs3/` | topo-9 / topo-10 / topo-11 / topo-12          |

## The control code

| file | role |
|------|------|
| `topology-supervisor.sh` | Top level, one per loop under systemd. Runs the build loop, repairs faults (at most `TOPOLOGY_MAX_REPAIRS`), escalates to `TOPOLOGY_ESCALATE_TO`. |
| `topology-build-loop.sh` | One iteration: check the statement registry, select a row, dispatch it to a seat through Agency (:7070), collect the nonce-bound EDN receipt, dispatch review, apply the verdict, commit. Resumes after a restart from the ledger and `runs*/inflight.edn`. |
| `build_step.bb` | The rules. Row selection, the state transition for each receipt outcome, the lemma DAG, and the `priorities` ranking strategy checkpoints use. |
| `worklist_check.bb` | Ledger invariants, checked before every write; a receipt that would break one is rejected and the ledger is left untouched. |
| `work-prompt.md`, `review-prompt.md` | What author/strategy seats and review seats are told, including the receipt format. |
| `extract_receipt.bb`, `inflight.bb` | Receipt parsing and the durable in-flight record. |
| `test-loop.sh`, `test-rejected-receipt.sh`, `test_gate_receipts.bb` | Tests of the transition rules; no agents are dispatched. |

Outside this directory, `problems/STATEMENTS.json` with
`scripts/statement-registry.py` pins every problem's approved Lean statement.
The loop refuses to run while any registered statement differs from its
approved fingerprint, so no seat can make a problem easier by editing it.
Statements change only through an outside fidelity grade and re-admission
(`statement-registry.py admit`). Design rationale:
`docs/TN-topology-build-loop-design.md`.

## Rows and states

A row has an `:id`, a `:kind` (`:reusable-theorem`, `:final-adapter`,
`:representation-comparison`, `:strategy-checkpoint`, `:lemma`, ...), a
`:state`, `:depends-on`, a `:scope` (the only files it may change) and an
`:acceptance` (declaration, type, required commands, allowed axioms).

- `:open` / `:repair`: eligible once every dependency is satisfied.
- `:done-unreviewed`: author finished; waiting for review.
- `:done`: a review PASSed a delivered result. Satisfies dependents.
- `:stopped`: a review PASSed a STOP, so the stop was honest but nothing was
  delivered. Satisfies no dependency and banks nothing. It reopens
  automatically when a lemma it reported missing is banked.
- `:needs-owner`: stopped twice (`TOPOLOGY_MAX_ROW_STOPS`) or failed review
  four times (`TOPOLOGY_MAX_ROW_FAILS`); waits for a human or a checkpoint
  re-route.
- `:blocked`: waiting on dependencies. `:superseded`: replaced.
- Lemma nodes (`:kind :lemma`) are `:backlog` or `:banked`. A PASS on the row
  that implements a lemma banks it; `sync-banked` also banks lemmas whose
  declarations already exist in the repo.

Rows with `:program true` are foundation programs: multi-job constructions
whose STOPs are progress checkpoints. They continue from their last commit for
up to `TOPOLOGY_PROGRAM_MAX_STOPS` jobs. `:campaign-priority` (lower first)
orders selection ahead of row kind.

Strategy checkpoints read `bb build_step.bb priorities LEDGER` and elect the
next rows for the highest-impact ready lemmas.

## Operating

All three units, with the seat and model settings, are launched by
`~/notes/closer/relaunch-loops.sh`, which starts only inactive units. Register
seats topo-1..12 in Agency first (with model `gpt-5.6-sol`), or the loops
auto-register onto colliding seats. Launch as user services, never as a
background child of an agent tool call, because that process group is reaped
when the call ends.

```bash
systemctl --user is-active topo1 topo2 topo3
systemctl --user stop topo1 topo2 topo3   # TERM keeps the in-flight job for reclaim
journalctl --user -u topo2
```

To edit a ledger or this code: stop the loops (they wait on a dirty tree
anyway), edit, run `bb worklist_check.bb LEDGER` and `./test-loop.sh`, commit
under `.git/topology-ledger-commit.lock`, relaunch. Owner additions to the
lemma DAG go through `bb build_step.bb add-lemmas LEDGER FILE`.

Useful reads:

```bash
bb build_step.bb priorities worklist3.edn   # per-problem backlog and ready lemmas
bb build_step.bb next-open worklist2.edn    # the row that runs next
bb worklist_check.bb worklist.edn           # validate; prints state counts
```

The ledger's git history is the audit trail: each transition is a
`topology-loop: record <row> transition <job>` commit, and each rule change is
a commit to this directory whose message names the incident behind it.
