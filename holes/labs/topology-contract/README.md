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

Launch it as a user service, not as a background child of an agent tool call:

```bash
systemd-run --user --unit=topology-build-loop --same-dir --collect \
  --setenv=PROBE_SEAT=codex-12 --setenv=AUTHOR_SEAT=codex-6 \
  --setenv=REVIEW_SEAT=codex-20 --setenv=STRATEGY_SEAT=codex-12 \
  --setenv=OWNER_SEAT=codex-18 --setenv=MAX_ITER=60 \
  /home/joe/code/apm-lean/holes/labs/topology-contract/topology-build-loop.sh
```

Inspect it with `systemctl --user status topology-build-loop` and
`journalctl --user -u topology-build-loop`; stop it with
`systemctl --user stop topology-build-loop`. Bare `nohup ... &` launched from
an agent command is not supported because that command's process group is
reaped when the tool call ends.

The supervisor sends Agency jobs, waits on their concrete job ids, applies the
nonce-bound EDN receipts, commits ledger transitions, and resumes after a
restart from the checked-in ledger and `runs/inflight.edn`. It retries transient
status failures, enforces `JOB_TIMEOUT`, and updates `runs/heartbeat.edn` while
waiting. Agency replies to the synthetic `topology-build-loop` sender are not a
continuation mechanism; job status and the durable in-flight record are the
authoritative channel. See
`docs/TN-topology-build-loop-design.md` for the strategic invariants.
