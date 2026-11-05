# tools: the scripts and agent instructions, as run

These files are copies of the ones used during the campaign, unedited. They
contain the original machine's paths and calls to its local coordination
server. They are here so the process can be read exactly and adapted, not
run as they are.

| file | what it is |
|---|---|
| `make-blueprint.md` | the procedure a blueprint author follows (summarised in [../02-blueprints.md](../02-blueprints.md)) |
| `library-split-preamble.md` | the packet for splitting one LIBRARY leaf into seat-sized leaves |
| `preamble.md` | the job text every seat received (seat-area style) |
| `prove-preamble.md` | the job text for full-copy seats in later rounds |
| `lemmatool.py` | `make` / `check` / `splice` / `path` for seat files; the mechanical checker |
| `next.sh` | dispatch: take the next leaf from the queue, make its file, send the job |
| `dispatch-tmpl.sh` | dispatch template for full-copy rounds |
| `land_problem.sh` | land a problem whose blueprint has no `sorry` |
| `merge_lemmas.sh` | merge the `lemmas` branch into `master` with checks |

## What to change to run them elsewhere

- **Paths.** `lemmatool.py` sets `W` (the lemma worktree) at the top. The
  shell scripts use `~/worktrees/apm-lean/lemmas` for the lemma worktree,
  `/home/joe/code/apm-lean` for the main checkout, and `~/notes/packets/lemmas`
  for the queue, job texts and round log.
- **Dispatch.** `next.sh` and `dispatch-tmpl.sh` send jobs with
  `agency_send.py --kind bell --mode work --park ...`. The `--park` part asks
  the server to wake the dispatcher when the seat replies. Replace that call
  with your own job queue. The dispatcher needs three things from it: start an agent
  session with the job text, return its final message, and start each job in a
  fresh session (`next.sh` resets the seat's session first).
- **Compile isolation.** The `flock /tmp/apm-lean-compile.lock` and
  `systemd-run --user --scope -p MemoryMax=12G` wrappers serialise compiles
  and cap their memory. Drop them on a machine with one seat. Keep something
  like them with several.
- **Reply handling.** Each job's reply was read by the agent that ran
  the round (claude-14). That agent ran `check`, `splice` and the landing script, and
  reviewed partial results by hand. That review is the part of the process
  that is not a script. [../03-lemma-seats.md](../03-lemma-seats.md)
  describes what it looks for.

`scripts/statement-registry.py`, which the landing script calls, is in the
repository and runs as is.
