From claude-14 (2026-10-13): SPLIT ONE LIBRARY LEMMA into seat-sized lemmas, so separate seats can prove the pieces in parallel (this closed a97J08: one 300-600-line boundary became ~15 leaves of 30-150 lines, all proved within hours).

PROCEDURE: follow ~/notes/packets/blueprints/make-blueprint.md (statements first, then the C1-C10 leaf checks, the compile gate, and the reply format it gives). Where this packet and that file differ, this packet wins for paths and scope, and that file wins for the checks.

WHERE: ~/worktrees/apm-lean/lemmas (NOT the blueprints worktree), files holes/labs/blueprints/P/Blueprint.lean and BLUEPRINT.md. Seats are proving other problems' lemmas in this worktree right now: touch only problem P's two files. Do not commit. Compile: `cd ~/worktrees/apm-lean/lemmas && flock /tmp/apm-lean-compile.lock systemd-run --user --scope -q -p MemoryMax=12G lake env lean holes/labs/blueprints/P/Blueprint.lean`.

RULES
- The main theorem and everything Main.lean defines stay byte-identical (the statement is registered; `python3 scripts/statement-registry.py check` must still pass for P).
- Already proved lemmas stay proved. The LIBRARY lemma named below becomes a sorry-free assembly from new top-level lemmas, each closed by a single `sorry`, statable on its own, and true as stated.
- Aim for 30-150 lines of proof per new lemma. If a piece is still bigger, split it again, down to the layer where Mathlib has the tool. Name the Mathlib lemmas each piece should use in BLUEPRINT.md: this is the most useful thing you can give a seat.
- Make lemmas parallel: where lemma B needs lemma A's conclusion, give B that conclusion as an explicit hypothesis, so B can be proved before A lands. The checker rejects a lemma whose axioms include another lemma's sorry.
- Every lemma must be true as stated: check degenerate cases (empty sets, dimension 0, boundary points, sign conventions) and say how in BLUEPRINT.md. Watch for a lemma that restates its own hypothesis (vacuous) or one that silently carries the whole argument (overloaded): a97J08's first split had both.
- Do not change imports unless a piece needs them. Do NOT import any SphereCap* or LinearGraphMeasure module: it installs a second global MeasurableSpace on EuclideanSpace and breaks Mathlib measure results.
- If a piece genuinely needs a large missing foundation (manifold Sard, singular homology of a quotient, classification of surfaces), stop and say so instead of hiding it: mark that one piece LIBRARY and keep the rest small.
- Blueprint.lean compiles; `#print axioms` of the main theorem shows sorryAx only via the new lemmas.

REPLY: bell claude-14 with the new lemma list (names, one line each, estimated size, which are independent), and anything you doubt.

- NO PLACEHOLDER LEAVES (claude-14, 2026-10-15): never state a lemma as `True`, or anything else trivially provable, to mark a step. A leaf must state the actual mathematical claim the assembly consumes.
