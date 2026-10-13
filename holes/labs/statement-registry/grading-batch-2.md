# Fidelity grades — batch 2 (2026-10-13)

Grader: read-only Claude subagent dispatched by claude-14; read problems/<id>/problem.md
(+ problem.tex, informal-solution.md) and problems/<id>/lean/Main.lean on branch `lemmas`.

| id | grade | decl | reason | prelim-defect |
|---|---|---|---|---|
| m99A01 | faithful | apm_m99a01 | extremals classified (iff) up to equality on [0,π/2] (repair 50c9a4310); candidate admissible; minimum direction right; no maximum. C² restriction disclosed, harmless (du Bois-Reymond) | none |
| t96A05 | faithful (one omission) | apm_t96a05 | the asked-for extension is encoded exactly; proof-guiding parts (a)–(c) omitted ((b)'s answer, "true" by the tube lemma, not recorded) | none |
| t02A07 | unfaithful (false) as graded | apm_t02a07 | IsTransverse compared the sum with ⊤ = ℝ⁴, but both summands lie in T_xX; density false. Fixed in the next commit (sum = T_xX; dim Z = 2 stated); needs re-grade | IsTransverse |

## m93J05 revoked (2026-10-13)
The registered statement (admitted faithful in batch 1) had part (c) backwards: `(∀ᶠ n, r ≤ J sₙ) → r ≤ J f`
is liminf J(sₙ) ≤ J f, false under weak convergence (sₙ = sin(2π(N+n)x) ⇀ 0, J(sₙ) = c_p > 0 = J 0, g = 0;
confirmed by an outside re-grade). Corrected in cee82c175 to J f ≤ liminf J(sₙ). Re-grade of the corrected
statement: "faithful-weak" ((e) states only the vanishing first variation). Re-admission after (e) is
strengthened to the explicit Euler–Lagrange system and re-graded.

## t02A07 re-grade after cc153cc91 (transversality against T_xX; dim Z = 2 stated)

| id | grade | decl | reason | prelim-defect |
|---|---|---|---|---|
| t02A07 | faithful | apm_t02a07 | IsTransverse is now the textbook notion (image of T_yS² + T_xZ = T_xX, vacuous off Z); true: λ² < 1/2 misses Z, λ² > 1/2 hits at regular points of y₂y₃, fails exactly at λ² = 1/2 (4 parameters), so dense; (a) regular value + finrank 2 | source typo (x²)² twice, repaired to the unit sphere |

Grader: read-only Claude subagent, 2026-10-13. Stale encoding note fixed in the same commit series.
