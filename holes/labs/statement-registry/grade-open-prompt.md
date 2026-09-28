You are grading formal statements of OPEN problems for FIDELITY, read-only, before they are entered in an approved statement registry. You have no stake in the outcome.

For each problem id in your list: read problems/<id>/problem.md (the prelim question) and the registered `theorem apm_<id>` in problems/<id>/lean/Main.lean (if absent, say so and name the declaration that actually states the problem, if any), together with every `apm_<id>_*` definition the statement uses, and any STATEMENT-REPAIR.md. Repo: /home/joe/code/apm-lean.

Grade the statement against problem.md:
- faithful: states the prelim claim (reasonable Lean encoding choices are fine)
- stronger: states more than asked, and is still true
- narrower: special case, mod-2 for integer, dropped part, extra hypothesis — say exactly what is dropped
- hypothesis-carries-core: a hypothesis supplies the main content the problem asks to prove
- vacuous: conclusion trivial or hypotheses unsatisfiable
- placeholder: the statement uses `opaque`, `axiom`, `sorry`-valued defs, or Prop parameters standing in for the mathematics
- false: the statement as encoded is false (give the counterexample)
Also flag PRELIM-DEFECT if problem.md itself is wrong or ambiguous in a way that forces a departure (give the evidence) — this is the only case in which a narrower statement can be accepted.
Quote the relevant Lean lines. Do not assume anything about how the statement came to be.

Rules: do not edit, build, commit or run lake. git show/log and reading files are fine.
Write your results to the output file named below as a markdown table (id | grade | decl | one-line reason | prelim-defect?) followed by a short evidence note per problem. Final message: the table only.
