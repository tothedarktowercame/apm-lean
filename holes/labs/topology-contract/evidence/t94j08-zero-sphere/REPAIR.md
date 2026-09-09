# Owner-authorized t94J08 specification repair, 2026-09-09

Request: claude-5, `invoke-1788982090497-16885-dd3cb200`; implementation: codex-15.

## Scope of the stop

Refill17's literal wording, "an exact mathematical refutation is established",
does support the broad reading taken by codex-12 and passed by codex-10. Their
proof and their historical interpretation are retained without alteration in
the ledger. However, the campaign's canonical mathematical/process documents
explicitly distinguish a false frozen consumer from termination of the portfolio:

- `TOPOLOGY-DEPENDENCY-DAG.md`, Node states: `SPEC-DEFECT` means "The source or
  frozen statement is false or materially mismatched" and requires "Repair both
  statement and paper trail before proof work". Its existing t96J07 false-statement
  entry is another consumer-local defect, not an end to the topology program.
- `docs/TN-topology-closure-experiments.md`, Stop rules: preserve the result,
  classify the node and "return to the portfolio".
- `docs/TN-topology-build-loop-design.md`, Strategic checkpoints: specification
  defects require an early checkpoint, and stopped evidence must remain addressable.
  SPEC-DEFECT transitions need an owner decision; this request supplies that
  authority conditionally on the evidence supporting a local defect.
- The full refill17 evidence and review explicitly say neither classical
  antipodal degree nor Sard is refuted. Its census still has 39 open consumers
  and 71 placeholders. The proved negation is the literal t94J08 conjunction,
  contradicted solely by its n=0 ordinary-H0 orientation requirement.

Thus the mathematical STOP is retained for the old encoding. The broad campaign
termination interpretation is superseded by an explicit owner resolution; it is
not dismissed as an invalid proof. Refill17 stays `:needs-owner` with its complete
evidence and review. A new dependent strategy checkpoint (refill18) is `:open`;
the existing validator/scheduler explicitly permits strategy recovery from
needs-owner dependencies. No state-machine or supervisor script is changed.

## Corrected frozen branch and coverage

`T94J08Sphere k` uses ambient dimension k. Hence `T94J08Sphere (n+1)` is Sⁿ,
including the two-point S⁰ when n=0. Ordinary integral H0 there has rank two.

The bridge and first main conjunct now require `1 ≤ n`; the local-index clause
requires `1 ≤ m`, i.e. ambient dimension m+1 at least two. Its proof supplies
that bound to the antipodal family. Existing degree definitions and ordinary
ModuleCat integral singular homology remain intact. This matches the DAG's
positive-dimensional sphere orientation/naturality route without replacing the
representation or adding assumed degree laws. The two existing placeholders
remain: this is a specification repair, not consumer closure.

Classical zero-sphere degree and one-dimensional local index remain legitimate
mathematics outside this newly frozen branch. A reduced-homology encoding is
needed to restore that coverage and must be separately elected. They are named
in Main, the DAG and the continuation's acceptance; no full-source coverage is
claimed.

Old Main SHA-256:
`f75c03843555aca28c4abd3c772c5cee3216e912c2c1d52255de75db719a2c3e`.
New Main SHA-256:
`cd3836746caa7a4f0aa3a9590ea78145227b2d63bfa0b22a596bdd2b7c02aeee`.
Old canonical HEAD inspected: `2de5e0b3560dc66d5ea84ecea765564bbee6f622`.
Historical row hashes remain historical; new t94J08 work must use the repaired pin.

## Retained counterexample and verification

The three adjacent `T94J08ZeroSphereRefutation*` files are byte-for-byte copies
of the reviewed /tmp artifacts. The Lean diagnostic includes the old proposition
and proves its exact negation; it does not import the newly repaired Main.
Its original Lean SHA-256 is
`b336d0daf658fe45acb4f63ded0203e92747e02359867eb953770d1747a57948`.
The source evidence and review job ids remain in refill16/17, including the
independent refill17 review `invoke-1788980274475-16845-85960495`.

Commands from the canonical apm-lean root (its own `.lake/packages` is the
ledger's canonical package authority, not a frame worktree):

```text
lake env lean problems/t94J08/lean/Main.lean
lake env lean holes/labs/topology-contract/evidence/t94j08-zero-sphere/T94J08ZeroSphereRefutation.lean
bb holes/labs/topology-contract/worklist_check.bb holes/labs/topology-contract/worklist.edn
```

The repaired Main elaborates with the existing two sorry sites; `apm_t94j08`
reports `[propext, sorryAx, Classical.choice, Quot.sound]`. The counterexample
reports only `[propext, Classical.choice, Quot.sound]`. Existing lint warnings
are retained; no axiom-clean closure of the repaired consumer is claimed.

Track 2's ledger, run history, seats and the shared Bash scripts are outside this
repair. Track 1 resumes through a user systemd supervisor with explicit track-1
paths and its previous codex-1/6/10/12 seat configuration.
