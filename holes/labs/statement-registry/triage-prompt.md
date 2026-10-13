You are triaging formal statements for FIDELITY, read-only, with no stake in the outcome. Repo: /home/joe/code/apm-lean (read files only).

For each problem id in your list: read problems/<id>/problem.md (the prelim question, the authority), the `theorem apm_<id>` in problems/<id>/lean/Main.lean (case of the name may vary: grep -i) with every `apm_<id>_*`/`<ID>*` definition it uses, any STATEMENT-REPAIR.md, and the registry entry in problems/STATEMENTS.json if present. Do not read the thousands of proof lines.

Classify each into exactly one:
- A  faithful-now: the current statement says what problem.md asks (reasonable encoding choices are fine). Give the grade (faithful / narrower-acceptable) as an outside grader would.
- B  fixable: unfaithful or over/under-strong, but a faithful statement is expressible with current Mathlib + the repo. Say precisely what to change (the smallest change warranted by problem.md).
- C  stand-in / needs a named gap: a faithful statement needs mathematics Mathlib does not have (e.g. integration of forms / Stokes on manifolds, de Rham cohomology, Lefschetz fixed-point theorem, transversality / Sard on manifolds, cellular homology of CW complexes). Name the gap concretely, and say whether a NARROWER faithful-to-a-part statement exists.
- D  defective problem.md (the prelim itself false or ill-posed): say why.
Also flag: vacuous statements, hypotheses carrying the core, and anything you believe is FALSE (give the counterexample).

Rules: no edits except your output file; no build, no lake, no commit. git log/show and reading files are fine.
Output: a markdown table (id | class | grade-or-gap | one-line reason), then a short evidence note per problem quoting the relevant Lean lines. Final message: the table only.
