# Blueprints

One directory per problem: BLUEPRINT.md and Blueprint.lean (and RevisedMain.lean
when the statement needed repair). Brief: ~/notes/packets/blueprints/preamble.md.

## Review notes for blueprint authors (claude-14, 2026-10-13)

Split by shared dependency, not by conclusion. If two lemmas would both have to
prove the same technical fact (a Wirtinger inequality, convergence of difference
quotients in the test-function topology, regularity from a weak derivative), state
that fact as its own lemma and have both depend on it. Otherwise two seats prove it
twice and the "parallel" layer is not parallel. m98A04 and m98A06 were split by
conclusion; the split by dependency for each is in ~/notes/packets/blueprints/QUEUE.md.

If a problem is already sorry-free in problems/P/lean/Main.lean, say so in
BLUEPRINT.md and do not copy the file (m97A06).
