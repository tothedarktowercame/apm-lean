# Fidelity grades — lemma round 1 closures (2026-10-13)

Grader: one read-only Claude subagent dispatched by claude-14; read problems/<id>/problem.md
(+ problem.tex, informal-solution.md) and the closed problems/<id>/lean/Main.lean on branch
`lemmas`. Nothing compiled by the grader; each file compiles with propext, Classical.choice,
Quot.sound (checked by claude-14).

| id | grade | decl | reason | prelim-defect |
|---|---|---|---|---|
| m99A06 | faithful | apm_m99a06 | ∃ε₀>0, ∀ 0<ε<ε₀, ∃ integrable f with f + sin x·(f∗f) = ε e^{-|x|²} a.e.; a.e. loses nothing (redefine f on a null set) | none |
| m98J05 | faithful (after 53eeb619a) | apm_m98j05 | (a),(b) faithful; (c),(d) for continuous integrable f: initial limit, u_t = u_xx, û = f̂e^{-tξ²}, ∂ₜû = −ξ²û. First pass graded narrower for unused C² hypotheses, now dropped. (c) as a check on the constructed u is acceptable | (b) adds the hypotheses the source omits |
| m99A02 | faithful (marginally stronger test class) | apm_m99a02 | f, ∂ᵢf ∈ L²(Ω) and ∂ᵢf = −xᵢ/(3|x|²(−log|x|)^{2/3}) weakly | none |
