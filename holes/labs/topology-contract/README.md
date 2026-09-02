# Topology build loop

Validate and exercise the loop without dispatching agents:

```bash
./test-loop.sh
./topology-build-loop.sh --dry-run
./topology-build-loop.sh --replay fixtures/t02A03-replay.edn
```

The checked-in `worklist.edn` contains the first portfolio seed derived from
the complete topology DAG: a `t00A01` van Kampen re-probe, the isolated
`t01A02` H2-degree probe, and a reviewed strategy checkpoint after those two
consumer outcomes. Configure distinct regular work/review seats and start the
supervisor:

```bash
PROBE_SEAT=codex-12 AUTHOR_SEAT=codex-6 REVIEW_SEAT=codex-20 \
  STRATEGY_SEAT=codex-12 \
  OWNER_SEAT=codex-18 nohup ./topology-build-loop.sh \
  > /tmp/topology-build-nohup.out 2>&1 &
```

The supervisor sends Agency jobs, waits on their concrete job ids, applies the
single-line EDN receipts, commits ledger transitions, and resumes after a
restart from the checked-in ledger. See
`docs/TN-topology-build-loop-design.md` for the strategic invariants.
