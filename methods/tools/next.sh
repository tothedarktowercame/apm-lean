#!/bin/bash
# next.sh SEAT: give SEAT the next lemma from round2.queue (make file from the
# current blueprint, commit it, bell the seat with a park that lands it).
s=$1; [ -f ~/notes/packets/lemmas/PAUSE ] && { echo "dispatch paused (rm ~/notes/packets/lemmas/PAUSE to resume); $s idle"; cat ~/notes/packets/lemmas/PAUSE; exit 0; }
# Seat cap (Joe 10-15, disk load): only seats listed in SEATS get work; others go idle.
[ -f ~/notes/packets/lemmas/SEATS ] && ! grep -qx "$s" ~/notes/packets/lemmas/SEATS && { echo "$s not in SEATS cap; idle"; exit 0; }
# 10-19: land.sh and next.sh hold the same lock, so a seat file is never made from a blueprint
# that land.sh has spliced but not yet committed (the diagonal seat failed its check that way).
exec 9>/tmp/apm-lemmas-land.lock; flock 9
Q=~/notes/packets/lemmas/round2.queue; W=~/worktrees/apm-lean/lemmas
line=$(head -1 "$Q"); [ -z "$line" ] && { echo "queue empty; $s idle"; exit 0; }
sed -i 1d "$Q"; set -- $line; p=$1; n=$2
# sed 1i is a no-op on an empty file (10-20: it would have dropped the lemma).
putback() { if [ -s "$Q" ]; then sed -i "1i $p $n" "$Q"; else echo "$p $n" > "$Q"; fi; }
# Never regenerate over uncommitted seat work (10-19: a proved, unlanded file was
# overwritten when its lemma was re-dispatched after a 429 duplicate).
if ! (cd $W && git diff --quiet -- holes/labs/lemmas/$p/$n.lean); then
  echo "$p/$n has uncommitted edits (unlanded proof?); put back, $s idle"; putback; exit 1; fi
cd $W && { python3 ~/notes/packets/lemmas/lemmatool.py make $p $n >/dev/null || { echo "make failed for $p/$n; put back"; putback; exit 1; }; } && git add holes/labs/lemmas/$p/$n.lean && \
  git commit -qm "lemmas: file for $p/$n (round 2)

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>"
b=~/notes/packets/lemmas/job-$n.md
{ cat ~/notes/packets/lemmas/preamble.md; printf '\nTHIS JOB: P = %s, NAME = %s. Your file: holes/labs/lemmas/%s/%s.lean. Proof sketch: %s and the review notes in holes/labs/blueprints/README.md.\n' $p $n $p $n "$(case $p in CT.*) echo ConstructionTargets/${p#CT.}.blueprint.md;; *) echo holes/labs/blueprints/$p/BLUEPRINT.md;; esac)"; [ -f ~/notes/packets/lemmas/notes/$n.md ] && cat ~/notes/packets/lemmas/notes/$n.md; } > $b
# Fresh thread per lemma: a long-lived seat thread overflows the context window
# (topo owners, 2026-10-13).
curl -s -m 20 -X POST -H 'Content-Type: application/json' -d '{}' "localhost:7070/api/alpha/agents/$s/reset-session" >/dev/null
out=$(cd ~/code/futon3c && python3 scripts/agency_send.py --from claude-14 --to $s --kind bell --mode work --park --park-deadline 14400 \
  --park-payload "round2 $p/$n back from $s: on PROVED run ~/notes/packets/lemmas/land.sh $p $n $s (land problem if 0 sorry); on BLOCKED-ON X append '$p $n' to round2.queue; on PARTIAL split it (banked aux lemmas) and queue the pieces. Then ~/notes/packets/lemmas/next.sh $s." < $b 2>&1 | grep -o '"job-id":"[^"]*"')
echo "$p $n $s $out" >> ~/notes/packets/lemmas/jobs.txt; echo "| $p | $n | $s | queued (round 2) |" >> ~/notes/packets/lemmas/STATUS.md
echo "$s <- $p/$n $out"
