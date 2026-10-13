# Fidelity grades — blueprint batch 1 (2026-10-13)

Graders: three read-only Claude subagents dispatched by claude-14, one per group, each reading
problems/<id>/problem.md (+ problem.tex, informal-solution.md), the candidate Lean file and the
diff of the change under review. Nothing compiled. Candidates: canonical problems/<id>/lean/Main.lean
for repairs already there; holes/labs/blueprints/<id>/RevisedMain.lean (branch `blueprints`) otherwise.

| id | candidate | grade | decl | reason | prelim-defect |
|---|---|---|---|---|---|
| m97A06 | Main (4a7a07fdb, 455d4d8c1) | faithful | apm_m97a06 | (a)–(d) match; Hessian at φ≡0 is ∫(η'²+η²) | partly: φ taken C² for the classical EL (du Bois-Reymond gives it anyway) |
| m95A03 | Main (03a2c1cb3) | **unfaithful (false)** | apm_m95a03 | Mathlib's IsMinOn f s u does not require u ∈ s; with p≡1, q≡0, f≡0 both v≡0 and v≡1 "minimise" over the admissible set, so part (c)'s uniqueness fails | the EqOn repair was right; a second defect remains. Revision queued |
| a00J04 | Main (8d22ab09f) | faithful | connectedComponents_complement_lemniscate_le | ENat.card ≤ N+1 with N ≥ 1 is the claim | no |
| b96A01 | Main (632fc800d) | narrower | apm_b96a01 | "nonabelian" in (d) is true but excludes more than the defect: the printed claim fails only for n = 1, G = C₂, p = 2 | yes (C₂ ⊂ GL₁(ℚ), p = 2). Tighter revision queued |
| m93J05 | Main (0b87e4577) | faithful | apm_m93j05 | Lᵖ-only directions is a necessary repair (toReal junk otherwise) | yes, encoding; (e) is stated as vanishing first variation |
| m96J02 | Main (96f495ecd) | narrower, justified | apm_m96j02 | local Lipschitz needed: x'' = √|x|, α = β = 0 has x = 0 and t⁴/144 | yes |
| a96A06 | RevisedMain | faithful | apm_a96a06 | restores the source's "simple pole at 1"; current Main is false | no (restores a source hypothesis) |
| m02J05 | RevisedMain | faithful | apm_m02j05 | a.e.-classes on [0,1]; old carrier breaks definiteness (1_[2,3]) | minor: "measurable functions" means classes for a norm |
| m96A02 | RevisedMain | faithful (part (a) slightly stronger) | apm_m96a02 | [Nonempty M]; u continuous on [0,1] (else u(0), u(1) unconstrained) | yes |
| m98J02 | RevisedMain | narrower, acceptable | apm_m98j02 | w₀ given by an L¹_loc function: T not hypoelliptic, so C² fails for arbitrary w₀; the informal solution's own hypothesis; such w₀ exists (Riemann function) | yes |
| m99J06 | RevisedMain | faithful (slightly stronger) | apm_m99j06 | full-sequence weak convergence, as the source asks (uₙ = P_{Vₙ}u*, norm convergence) | no; the old subsequence form was an unwarranted narrowing |

Full grader reports: this session's transcript (claude-14, 2026-10-13).

## Re-grade: m95A03 (RevisedMain, b1207c9c1)

| id | candidate | grade | decl | reason | prelim-defect |
|---|---|---|---|---|---|
| m95A03 | RevisedMain | faithful | apm_m95a03 | part (c) witness now admissible; uniqueness on [a,b] over all C¹ admissible minimisers (J(v) = J(u) + ∫p(v−u)′² + q(v−u)²); (a), (b) unchanged and true; non-vacuous (p = 1, q = f = 0) | none remaining |

Grader: read-only Claude subagent, 2026-10-13.
