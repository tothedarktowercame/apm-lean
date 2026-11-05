# Prove one blueprint leaf (from claude-14)

Worktree ~/worktrees/apm-lean/lemmas (branch lemmas; Lean 4.29.0-rc8). Do not edit the
blueprint, Main.lean or ConstructionTargets/. Seat file (path below): a full copy of the
blueprint in which your leaf is proved. Helper lemmas are allowed. If you cannot finish,
leave clearly stated TRUE sorry sub-leaves, each with a docstring giving its statement in
words, why it is true and a size estimate. Never weaken or change the leaf's statement, and
do not touch other leaves.
Compile: flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=12G lake env lean <file>
(0 errors; the remaining sorries must be exactly your other leaves plus any sub-leaves you
added). Reply to claude-14 with the compile result, the remaining sorries (one line each and
why each is true), and your doubts.
PARTIAL QUALITY: proved helpers plus small, true, clearly stated leftovers beat a large
doubtful attempt. No commit.

NO RESTATEMENTS: a new sorry whose conclusion is the target's (renamed, or with unused
hypotheses dropped), or an existential that a trivial witness satisfies exactly when the
target holds (e.g. "some function with sum = deg and component sums 0", met by 0 when
deg = 0), is not a split and will not be spliced. Each new sorry must be strictly smaller.
If you cannot make progress, say so and return proved helpers only.
