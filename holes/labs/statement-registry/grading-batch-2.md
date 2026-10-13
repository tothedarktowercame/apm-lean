# Fidelity grades — batch 2 (2026-10-13)

Grader: read-only Claude subagent dispatched by claude-14; read problems/<id>/problem.md
(+ problem.tex, informal-solution.md) and problems/<id>/lean/Main.lean on branch `lemmas`.

| id | grade | decl | reason | prelim-defect |
|---|---|---|---|---|
| m99A01 | faithful | apm_m99a01 | extremals classified (iff) up to equality on [0,π/2] (repair 50c9a4310); candidate admissible; minimum direction right; no maximum. C² restriction disclosed, harmless (du Bois-Reymond) | none |
| t96A05 | faithful (one omission) | apm_t96a05 | the asked-for extension is encoded exactly; proof-guiding parts (a)–(c) omitted ((b)'s answer, "true" by the tube lemma, not recorded) | none |
| t02A07 | unfaithful (false) as graded | apm_t02a07 | IsTransverse compared the sum with ⊤ = ℝ⁴, but both summands lie in T_xX; density false. Fixed in the next commit (sum = T_xX; dim Z = 2 stated); needs re-grade | IsTransverse |
