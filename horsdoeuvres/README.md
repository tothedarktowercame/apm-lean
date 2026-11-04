# Hors d'oeuvres

These problem bundles sit outside the main deliverable in `problems/`. Being here does not
mean we offer a solution for them. Each one keeps its bundle (`problem.tex`, `problem.md`,
`informal-solution.md`, `status.json`) unchanged; only the location moved (Joe, 2026-11-04).

## broken/: not counted

| Problem | Reason |
|---|---|
| a98J05 | Source incomplete: the 2002 transcription gives a hypothesis on f(z) = z + Σ cₙzⁿ but no question. |
| t98J04 | Source incomplete: part (b) needs a diagram the corpus does not have; the curve is described only in words. Part (a) (linked circles) is provable but the problem is not stated whole. |
| lts-derived-induction-lem3 | Not APM: from another series (Borel-equivariant spectra). |
| lts-monadic-integration | Not APM: from another series (measure monad / Pettis integrals). |

## viable/: candidates for the main section

There is no Lean statement yet because a faithful statement needs definitions that 4.29
Mathlib lacks. This means a different workflow (vocabulary first, then statement, then
proof), not a reason to skip a problem. A problem moves back to `problems/` when it has a
registered statement.

| Problem | Vocabulary needed |
|---|---|
| t93A05 | mod-2 and oriented intersection numbers of submanifolds of ℝP³; homotopy classes S² → ℝP³ |
| t93J05 | integration of a 2-form over a piecewise-smooth oriented surface in ℝ³ |
| t95A05 | compact codimension-0 submanifold with boundary separating closed sets; closed (n−1)-forms and their integrals over the boundary |
| t98J05 | genus-2 surface in ℝ³, its quotient by rotation, pullback of 1-forms through a covering and a quotient |
| t99A05 | mod-2 degree and mod-2 intersection number I₂ |
| t99A06 | Euler characteristic of a manifold (Mathlib's is for algebraic complexes); submersions to S¹ |

Earlier analysis: `docs/statement-encoding-skips-2026-09-07.md`,
`docs/statement-construction-roundup-2026-09-10.md`.
