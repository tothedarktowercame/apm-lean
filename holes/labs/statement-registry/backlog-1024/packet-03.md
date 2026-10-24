You are grading formal statements for FIDELITY, read-only. You have no stake in the outcome.

For each problem id in your list (file given below): read problems/<id>/problem.md (the prelim question) and the registered `theorem apm_<id>` in problems/<id>/lean/Main.lean, together with every `apm_<id>_*` definition that theorem uses. Repo: /home/joe/code/apm-lean. Also read problems/<id>/STATEMENT-REPAIR.md if present.

Grade the CURRENT statement against problem.md:
- faithful: states the prelim claim (reasonable Lean encoding choices are fine)
- stronger: states more than asked
- narrower: a real restriction (special case, mod-2 for integer, extra hypothesis) — say exactly which
- hypothesis-carries-core: a hypothesis supplies the main mathematical content the problem asks to prove — say which
- vacuous: conclusion trivial or hypotheses unsatisfiable
Quote the relevant Lean lines.

If the list marks the problem REPAIRED, also compare with the bank encoding (git show <first-sha>:problems/<id>/lean/Main.lean) and classify each repair commit neutrally:
- correction: the bank statement was wrong (false, mis-parsed, mis-typed, did not say what problem.md says) and the repair fixes it
- improvement: the bank statement was acceptable and the repair is closer to problem.md
- neutral: equivalent restatement
- narrowing: the repair makes the statement say less than the bank version did
Do not assume a change is bad because it changed. Give the evidence either way. If the old statement was false, say so and cite any refutation in the file.

Rules: do not edit, build, commit or run lake. git show/log and reading files are fine.
Write your results to the output file named below as a markdown table (id | grade | one-line reason | repair classification if any) followed by a short evidence note per problem. Final message: the table only.


Your list (10 problems, none marked REPAIRED; do the repair comparison only if the file history shows the theorem statement was changed after it was first committed): holes/labs/statement-registry/backlog-1024/list-03
  m01J06 m02A02 m02A03 m02A05 m02A06 m02J01 m02J03 m02J04 m02J06 m03J01
Output file: /home/joe/code/apm-lean/holes/labs/statement-registry/backlog-1024/grades-03.md

Context: these problems are closed (no sorry) but their statements were never graded. A vacuous, narrower or hypothesis-carries-core grade reopens the problem, so be exact. Check smoothness orders: a bare ⊤ as a smoothness order in this Mathlib is analytic (ω), not C^∞. Also flag any `axiom`, `opaque` or `sorry`-typed definition the theorem depends on.

Do not commit; the output file stays uncommitted for review. When done, bell claude-14 back with the table.
