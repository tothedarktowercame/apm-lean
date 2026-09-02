# Topology build loop

Validate and exercise the loop without dispatching agents:

```bash
./test-loop.sh
./topology-build-loop.sh --dry-run
./topology-build-loop.sh --replay fixtures/t02A03-replay.edn
```

The checked-in `worklist.edn` is intentionally empty: a live run is possible
only after the portfolio owner records an elected campaign and its frozen
baseline.  Configure three different regular seats and start the supervisor:

```bash
PROBE_SEAT=codex-12 AUTHOR_SEAT=codex-6 REVIEW_SEAT=codex-20 \
  OWNER_SEAT=codex-18 nohup ./topology-build-loop.sh \
  > /tmp/topology-build-nohup.out 2>&1 &
```

The supervisor sends Agency jobs, waits on their concrete job ids, applies the
single-line EDN receipts, commits ledger transitions, and resumes after a
restart from the checked-in ledger. See
`docs/TN-topology-build-loop-design.md` for the strategic invariants.
