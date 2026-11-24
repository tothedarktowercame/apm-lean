# Statement and proof notes from the reader-clear sample (2026-11-24)

Filed by claude-12 from futon6 `holes/M-reader-clear.md`. Two reader seats (one Codex, one
Zai) read the PaperPrinter render of 27 proved problems beside the informal proof and asked
questions; a Codex seat holding `Main.lean` answered. Most findings were about the print and
went to the cleanup lab. The ones below are about the statements, the Lean proofs, or the
informal solutions. They are reading results: nothing here has been regraded, and no Lean
file was changed. Line numbers are those of `Main.lean` on 2026-11-24.

## Statements for the repair pool to look at

| Problem | Finding | Checked how |
|---|---|---|
| a98J01 | The theorem assumes `Measurable f` for f : ℝ → ℝ (Borel, whole line); the problem is Lusin's theorem for Lebesgue measurable f on [a,b]. Zero extension and change on a null set are not formalised; header says "Statement repairs: None" (58-66). | read by claude-12 |
| t91J05 | Main theorem assumes `[ConnectedSpace X]` (709-713); the problem asks which spaces can be a finite cover, and `IsFiniteCover` allows disconnected ones. Mentioned in header prose, not listed as a repair. | removing the instance fails to compile |
| m03J02 | `IsM03J02Solution` imposes the equation at every real t; the problem poses it for t > 0. The file comment gives the reason (uniqueness fails otherwise for functions on ℝ). | read by the answering seat; not judged |
| a97A02 | t ∈ [0,1] in the estimate is unused. | generalised copy compiles (codex-18) |
| aunk05 | Hypothesis that Ω is connected is bound and unused. | copy without it compiles |
| b93A04 | The theorem states the join of the two fixing subgroups; the problem writes the product set H₁H₂. Equal under normality, but that step is not in the Lean. | read by the answering seat |
| m03J05, m98A06, t96A08, m02J04 | Points raised by control-set readers about hypotheses and domains. | experiments in progress; see below |

## Lean proofs that do not carry out what the problem asks

| Problem | Finding |
|---|---|
| t97J07 | Part (c): χ(ℂP²) = 3 and the fixed-point contributions summing to 3 are proved separately; no Lefschetz–Hopf statement links them (322-373, 140-142). The line contribution is 2 × sign with the 2 hard-coded (76-94). |
| m01J01 | Both parts are single library calls (`ContinuousLinearMap.isOpenMap`, `LinearMap.continuous_of_isClosed_graph`); in the implication the open-mapping assumption is bound as `_` and unused. |
| m03J02 | Part (a) says "Use the contraction mapping theorem"; existence and uniqueness are cited from Mathlib's Picard–Lindelöf and ODE uniqueness results (40-47, 74-82, 106, 221, 233). |
| t94A05 | The problem says "Do not quote any theorems you do not prove"; the proof is `ChartedSpace.locPathConnectedSpace` then `pathConnectedSpace_iff_connectedSpace`. |
| b03J04 | Irreducibility of X^p − β is one call to `X_pow_sub_C_irreducible_iff_of_prime` (91-96). |
| aunk05 | Two library calls (`TendstoLocallyUniformlyOn.differentiableOn`, `.deriv`). |
| t03J06 | The theorem is about two parametrisation integrals; that their images make up the surface with the stated orientation is a comment, not a statement. A reader checked the value 7π by hand. |
| a98J01 | Proof is `Measurable.exists_continuous` plus `borel_eq_borel_of_le` and inner regularity, not the Lusin argument of the informal solution. |

## Unused declarations

t91J05 Declaration 19 (Euler-characteristic lemma, cited by nothing); a98J02 Declaration 6
(deleting it compiles); aunk04 `apm_aunk04_rouche_bound` (33-44; the file still imports
`ConstructionTargets.Rouche`); m99J02 `Continuous q` used only for integrability (322).

## Informal solutions (errata)

- t91J05: "the number of sheets is finite since the base is compact and the cover connected" is false (ℝ → S¹).
- t94A05: "an open subset of ℝⁿ is path connected" is false; use a ball in the chart image.
- b03J04: multiplies a root of unity from an unspecified extension by α in K with no common field.
- a92J05: closing remark (a single dominating term exists for any polynomial on any circle) is false: z² + 3z + 3 on |z| = 1.
- a96J04: `informal-solution.md` embeds a stale Lean statement (closed intervals; Main.lean 223-228 has open ones).
- a98J01: the separation constant is a minimum over compact sets that may be empty or fewer than two.
- a97A02: the symmetric difference has measure 2·min(|s−t|, 2h), not 2|s−t|.
- a03J01: "potentially uncountable collection" for a sequence of sets.
- t95A03: "B₂ ⊆ B₁" is not given by the cover and not needed.
- m93J03: uniqueness is obtained only inside a neighbourhood from the implicit function theorem; not checked against the Lean statement.
- m02J04: finds a stationary catenary without proving it minimal; the Lean proof does prove it.

## Unproved though zero-ink

t99A04, t97A06, t02A08 contain `sorry` and were drawn into the sample because the sample
filter looked only at residual ink.
