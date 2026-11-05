#!/bin/bash
P=~/notes/packets/lemmas; base=97a57ea462; prob=t95J06
send() { pk=$1; seat=$2; seatfile=leaf_${pk#leaf-}.lean
  W=~/worktrees/apm-lean/lemmas; [ -e $W/holes/labs/lemmas/$prob/$seatfile ] || git -C $W show $base:holes/labs/blueprints/$prob/Blueprint.lean > $W/holes/labs/lemmas/$prob/$seatfile
  cat $P/prove-preamble.md $P/$prob/$pk.md | python3 ~/code/futon3c/scripts/agency_send.py --from claude-14 --to $seat --kind bell --mode work --park --park-deadline 3600 --park-payload "Wake: $prob $pk from $seat. Checklist: 1) compile holes/labs/lemmas/$prob/$seatfile; 2) full copy; no restated sub-leaves (unpacking ∀/∃, equivalent statements, trivially-witnessed existentials, renamed remainder count); new sub-leaves true; 3) splice via git merge-file against base $base onto current blueprint, compile (0 errors), registry check, commit; 4) dispatch what remains; 5) report to Joe; deadline: job state." 2>&1 | grep -o '"job-id":"[^"]*"\|park-[0-9a-f-]*'
  echo "--- $pk -> $seat"; }
