# F218 apparatus intervention: progress-contract conflict

The original close trace is rejected specifically by `progressTraceValid`.
Its only progress observation is enabled=true, elapsedMs=532092,
validExternalWait=true, semanticCursorAdvanced=false, coordinatorDisabled=false,
firstViolationRecorded=false. Other observation groups pass.

The Lean predicate in `DarkTower/APMCampaignTraceChecker.lean` requires elapsed
<=300000 for an enabled coordinator even when its external wait is valid.
The live semantic watchdog instead accepts an external wait through its declared
job deadline plus grace (`futon3c/.../semantic_progress_watchdog.clj`,
`valid-external-wait?`). Consequently the runtime can legitimately keep working
under its own contract yet produce a trace refused at closure. This is not
established as a store timeout or a proof failure.

Intervention completed: the checker now emits the failed predicate and offending
progress row on rejection. Its acceptance predicate is unchanged. Offline replay
and explicit synthetic 300000/300001 boundary controls are retained by `check.py`
and `results.json`. No real trace, closure receipt or APM ledger was rewritten.

F218 is **not recovered**: the conflicting invariant needs a structural repair.
Proposed successor contract: retain absolute job deadline, observed time and
wait authority identity in each progress observation. A valid external wait
must prove it is within that bound; a no-wait period must meet the semantic
progress budget. Review the same predicate for the watchdog and Lean checker,
with expired-wait, absent-authority, no-progress and boundary controls. This is
an explicit contract revision, not a local exception for F218. Existing evidence
must remain pinned; recovery may only use independently verifiable retained
wait authority, never fabricated timestamps or a clipped elapsed duration.

Until that contract is reviewed and implemented, keep F218 parked for apparatus
repair. Diagnostics improve the next refusal but do not make this failed closure
successful. Joe's workarounds-forbidden instruction is the reason to stop at
this invariant conflict rather than force a replay to pass.
